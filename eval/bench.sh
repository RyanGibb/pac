#!/usr/bin/env bash
# Resolution time and memory, pac in each order against each ecosystem's
# own tool, asked what eval/<eco>/scale.sh asks and invoked as it invokes
# them.
#
# Per query, one warm-up round and then REPS measured rounds.  A round runs
# every variant once, so a drift in the machine lands on all of them alike
# rather than on whichever ran last.  One measured process at a time; the
# only other processes are the index servers cargo and npm are pointed at,
# idle between their requests.  No query starts at a load average of
# LOADSTART or more, and one whose block ends at LOADMAX or more is
# measured again, up to three times.
#
# Wall is taken around GNU time, whose own start-up is what `floor`
# measures, with PIN, a command prefix such as `taskset -c 2`, in front of
# both.  RSS is GNU time's %M, the largest single process in the measured
# tree, so it leaves out the index servers.  Every row lands in
# $RUN/res/<step>/<set>/<key>.csv, written whole when its block completes,
# and a query already there is skipped: after a crash, rerun the same line.
#
# The sets are the regression set, `regress`, and, where STRAT holds
# <eco>.q, as stratify.py writes it, `strat`.  outliers.txt names the
# queries too slow for REPS rounds: their step leaves them out, and
# `outliers` measures them OREPS times each under OCAP, with a warm-up for
# the tool alone.
#
# usage: bench.sh <step>...    step: info floor debian debian-cold alpine
#          opam opam-cold cargo npm npm-shared npm-placement outliers
# env: RUN (outside the source tree), PAC (default _build/default/bin/main.exe),
#      REPS (5), CAP (seconds, 0 for none), OREPS (3), OCAP (1800),
#      STRAT, SETS (regress strat), PIN, LOADSTART (2.5), LOADMAX (3.5), PORT (cargo's proxy,
#      8991), NPORT (npm's shim, 8899), DEPTH (placement's --depth, 8)
# Run inside `nix develop ./nix`, with no ocamlc on PATH: opam reads
# sys-ocaml-version off whatever ocamlc it finds.
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
TOP="$(cd "$S/.." && pwd)"
RUN="${RUN:?set RUN to a run directory outside the source tree}"
PAC=$(realpath "${PAC:-$TOP/_build/default/bin/main.exe}")
REPS="${REPS:-5}" CAP="${CAP:-0}" OREPS="${OREPS:-3}" OCAP="${OCAP:-1800}"
STRAT="${STRAT:-}" SETS="${SETS:-regress strat}" PIN="${PIN:-}"
LOADSTART="${LOADSTART:-2.5}" LOADMAX="${LOADMAX:-3.5}"
GTIME="${GTIME:-$(readlink -f /run/current-system/sw/bin/time)}"
APT="${APT:-apt-get}" DEPTH="${DEPTH:-8}"
export PORT="${PORT:-8991}" NPORT="${NPORT:-8899}"
mkdir -p "$RUN" && RUN=$(cd "$RUN" && pwd)
cd "$TOP" || exit 1
. "$S/serve.sh"
BG=()

log() { printf '%s %s\n' "$(date -u +%FT%TZ)" "$*" | tee -a "$RUN/bench.log"; }
load1() { cut -d' ' -f1 /proc/loadavg; }
below() { awk -v a="$1" -v b="$2" 'BEGIN { exit !(a < b) }'; }

quiet() {
  local l
  while l=$(load1); ! below "$l" "$LOADSTART"; do
    log "load $l, waiting"
    { date -u; top -b -n 1 -w 200 | head -n 30; } >> "$RUN/load.log"
    sleep 60
  done
}

# EPOCHREALTIME is a builtin, so no fork sits inside the timed interval
# beyond the measured command's own
elapsed() {
  local d=$(( ${2/./} - ${1/./} ))
  printf '%d.%06d' $((d / 1000000)) $((d % 1000000))
}

run1() {  # <step> <query> <variant> <rep> <cap> <out> <command...>
  local step=$1 q=$2 var=$3 rep=$4 cap=$5 out=$6 t0 t1 rc rss parse solve
  shift 6
  : > "$RUN/rss"
  if [ "$cap" = 0 ]; then
    t0=$EPOCHREALTIME
    $PIN "$GTIME" -f %M -o "$RUN/rss" "$@" < /dev/null > "$out" 2>&1
    rc=$?
    t1=$EPOCHREALTIME
  else
    t0=$EPOCHREALTIME
    timeout -k 10 "$cap" $PIN "$GTIME" -f %M -o "$RUN/rss" "$@" < /dev/null > "$out" 2>&1
    rc=$?
    t1=$EPOCHREALTIME
  fi
  rss=$(tail -n 1 "$RUN/rss")
  case $rss in *[!0-9]*|'') rss= ;; esac
  parse=$(sed -n 's/^parse \([0-9.]*\)s$/\1/p' "$out" | tail -n 1)
  solve=$(sed -n 's/^solve \([0-9.]*\)s$/\1/p' "$out" | tail -n 1)
  printf '%s,%s,"%s",%s,%s,%s,%s,%s,%s,%s,%s,%s\n' "$step" "$SET" "$q" "$var" "$rep" \
    "$(elapsed "$t0" "$t1")" "$parse" "$solve" "$rss" "$rc" "$(date -u +%FT%TZ)" "$(load1)" >> "$ROWS"
}

# Each step supplies argv_<eco> <variant> <key> <query>, setting CMD and
# DIR, and may supply pre_<eco> <variant> <key> <query>, run untimed before
# each measured run; a variant pac-<order> is pac in that order
measure() {  # <step> <key> <query> <variant> <rep> <cap>
  local step=$1 k=$2 q=$3 v=$4 r=$5 cap=$6 e=${1%-*} o
  if declare -F "pre_$e" > /dev/null; then "pre_$e" "$v" "$k" "$q" < /dev/null ||
    { log "$step $q $v: pre-step failed, not measured"; return 1; }; fi
  "argv_$e" "$v" "$k" "$q"
  o="$RUN/out/$step/$SET/$k.$v"
  case $r in 0|1|cold) o="$o.$r" ;; *) o="$o.last" ;; esac
  pushd "$DIR" > /dev/null || return 1
  run1 "$step" "$q" "$v" "$r" "$cap" "$o" "${CMD[@]}"
  popd > /dev/null || return 1
}

order() { printf -- '--order=%s' "${1#pac-}"; }

# the set's queries as key<TAB>query, less the outliers of the step
queries() {  # <step> <eco>
  case $SET in
    regress) if [ "$2" = npm ]; then awk '{print $1 "@" $2}' "$S/npm/baseline/roots.txt"
             else cat "$S/$2/queries.txt"; fi ;;
    strat) [ -z "$STRAT" ] || [ ! -e "$STRAT/$2.q" ] || awk -F'\t' '{print $NF}' "$STRAT/$2.q" ;;
  esac | python3 "$S/triage_lib.py" keys |
    awk -F'\t' 'FILENAME != "-" {out[$0]; next} !($2 in out)' <(sed -n "s/^$1 //p" "$S/bench/outliers.txt") -
}

block() {  # <step> <key> <query> <variant>...
  local step=$1 k=$2 q=$3 dest try r v l
  shift 3
  dest="$RUN/res/$step/$SET/$k.csv"
  [ -s "$dest" ] && return 0
  mkdir -p "$RUN/res/$step/$SET" "$RUN/out/$step/$SET"
  for try in 1 2 3; do
    quiet
    ROWS="$dest.tmp"; : > "$ROWS"
    for r in $(seq 0 "$REPS"); do
      for v in "$@"; do measure "$step" "$k" "$q" "$v" "$r" "$CAP"; done
    done
    l=$(load1)
    if below "$l" "$LOADMAX" || [ "$try" = 3 ]; then
      mv "$ROWS" "$dest"
      log "$step/$SET $q done (load $l)"
      return 0
    fi
    log "$step/$SET $q load $l at the end of its block, measuring it again"
  done
}

# one run per variant, with the files it reads out of the page cache first:
# without root there is no drop_caches, so this is posix_fadvise(DONTNEED)
# on the index, the tool's state, pac and the tool's store path, which
# leaves the kernel's dentry and inode caches warm
cblock() {  # <step> <key> <query> <evict paths> <variant>...
  local step=$1 k=$2 q=$3 ev=$4 dest v
  shift 4
  dest="$RUN/res/$step/$SET/$k.csv"
  [ -s "$dest" ] && return 0
  mkdir -p "$RUN/res/$step/$SET" "$RUN/out/$step/$SET"
  quiet
  ROWS="$dest.tmp"; : > "$ROWS"
  for v in "$@"; do
    python3 "$S/bench/evict.py" $ev >> "$RUN/evict.log" 2>&1
    measure "$step" "$k" "$q" "$v" cold "$CAP"
  done
  mv "$ROWS" "$dest"
  log "$step/$SET $q done (load $(load1))"
}

# each set of a step, every query a block, or with evict paths a cold one
sets() {  # <step> <eco> <evict paths or ""> <variant>...
  local step=$1 eco=$2 ev=$3 k q
  shift 3
  log "== $step start: $(uptime)"
  for SET in $SETS; do
    while IFS=$'\t' read -r k q <&3; do
      if [ -n "$ev" ]; then cblock "$step" "$k" "$q" "$ev" "$@"; else block "$step" "$k" "$q" "$@"; fi
    done 3< <(queries "$step" "$eco")
  done
  log "== $step end: $(uptime)"
}

store() { local p; p=$(readlink -f "$(command -v "$1")"); dirname "$(dirname "$p")"; }

argv_debian() {
  DIR=$TOP
  case $1 in
    pac-*) CMD=("$PAC" debian $(order "$1") --native amd64 repos/debian/Packages $3) ;;
    apt) CMD=("$APT" -s install $3) ;;
  esac
}
setup_debian() {
  [ -s "$RUN/aptroot/var/cache/apt/pkgcache.bin" ] ||
    bash "$S/debian/setup.sh" "$RUN/aptroot" > "$RUN/apt-setup.log" 2>&1 ||
    { log "debian setup failed"; return 1; }
  export APT_CONFIG="$RUN/aptroot/etc/apt/apt.conf"
}

argv_alpine() {
  DIR=$TOP
  case $1 in
    pac-*) CMD=("$PAC" alpine $(order "$1") repos/alpine/APKINDEX $3) ;;
    apk) CMD=("$APK" add --root "$RUN/apkroot/root" --usermode --allow-untrusted
              --no-network --repository "$RUN/apkroot/repo" --simulate $3) ;;
  esac
}
setup_alpine() {
  [ -s "$RUN/apkroot/repo/x86_64/APKINDEX.tar.gz" ] ||
    bash "$S/alpine/setup.sh" "$RUN/apkroot" > "$RUN/apk-setup.log" 2>&1 ||
    { log "alpine setup failed"; return 1; }
  APK=$(sed -n 's/^export APK=//p' "$RUN/apk-setup.log")
}

argv_opam() {
  DIR=$TOP
  case $1 in
    pac-*) CMD=("$PAC" opam --opam-version "$OV" $(order "$1") repos/opam-repository $3) ;;
    opam) CMD=(opam install $3 --dry-run --solver=builtin-0install --switch cmp --no-depexts -y) ;;
  esac
}
setup_opam() {
  if command -v ocamlc > /dev/null; then
    log "ocamlc on PATH ($(command -v ocamlc)): opam would read sys-ocaml-version from it"
    return 1
  fi
  export OPAMROOT="$RUN/opamroot"
  [ -d "$OPAMROOT/cmp" ] || bash "$S/opam/setup.sh" "$OPAMROOT" > "$RUN/opam-setup.log" 2>&1 ||
    { log "opam setup failed"; return 1; }
  OV=$(opam --version)
}

# The manifest is the one scale.py writes, self-patched where pac's answer
# merges the root with its registry copy, so it is asked of pac once,
# untimed, before the first round
pre_cargo() {
  local w=$CARGO_CMP_OUT/work/$3
  [ -e "$w/.asked" ] || PAC=$PAC python3 -c '
import sys; sys.path.insert(0, sys.argv[1]); import run_query
sys.exit(run_query.ask_pac(sys.argv[2])[1] is None)' "$S/cargo" "$3" || return 1
  touch "$w/.asked"
  rm -f "$w/Cargo.lock"
}
argv_cargo() {
  DIR=$TOP
  case $1 in
    pac-*) CMD=("$PAC" cargo "$TOP/repos/crates.io-index" "$CARGO_CMP_OUT/work/$3/Cargo.toml"
                --rust-version "$RUSTV" --print-parents $(order "$1")) ;;
    cargo) CMD=(cargo generate-lockfile --manifest-path "$CARGO_CMP_OUT/work/$3/Cargo.toml") ;;
  esac
}
setup_cargo() {
  export CARGO_CMP_OUT=$RUN/cargo CARGO_HOME=$RUN/cargo/cargo-home
  python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import run_query as r
r.check_toolchain(); r.write_cargo_config()' "$S/cargo" || return 1
  RUSTV=$(python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import run_query as r
print(r.installed_rustc())' "$S/cargo")
  [ -z "${PROXY:-}" ] || return 0
  serve "$PORT" "$TOP/repos/crates.io-index" "$RUN/cargo/proxy.log" \
    python3 "$S/cargo/sparse_proxy.py" "$PORT" "$TOP/repos/crates.io-index" || return 1
  PROXY=$served; BG+=("$served"); trap 'kill "${BG[@]}" 2> /dev/null' EXIT
}

# npm's own cache persists across runs, as it does across one run's queries
pre_npm() {
  local w=$NPM_RUN/work/$2
  if [ ! -s "$w/package.json" ]; then
    mkdir -p "$w"
    node "$S/npm/root.js" "$NPM_RUN/cache" $3 > "$w/package.json.new" && mv "$w/package.json.new" "$w/package.json" ||
      return 1
  fi
  rm -f "$w/package-lock.json"
}
argv_npm() {
  DIR=$TOP
  case $1 in
    pac-*)
      if [ "$READING" = placement ]; then set -- "$@" --depth "$DEPTH"; else set -- "$@" --tree; fi
      CMD=("$PAC" npm $(order "$1") --reading="$READING" "${@:4}" --cache "$NPM_RUN/cache"
           --node-version "$NODEV" --npm-version "$NPMV" $3) ;;
    npm)
      DIR=$NPM_RUN/work/$2
      CMD=(npm install --package-lock-only --loglevel=http --registry "http://127.0.0.1:$NPORT"
           --cache "$NPM_RUN/home/npmcache" --userconfig "$NPM_RUN/home/.npmrc"
           --globalconfig "$NPM_RUN/home/npmrc-global" --no-audit --no-fund --no-update-notifier) ;;
  esac
}
setup_npm() {
  NPM_RUN=$RUN/npm
  [ -d "$NPM_RUN/cache" ] || bash "$S/npm/setup.sh" "$NPM_RUN" > "$RUN/npm-setup.log" 2>&1 ||
    { log "npm setup failed"; return 1; }
  mkdir -p "$NPM_RUN/bin"
  printf '#!/bin/sh\nprintf 404; exit 22\n' > "$NPM_RUN/bin/curl"
  chmod +x "$NPM_RUN/bin/curl"
  NPMV=$(sed -n 1p "$S/npm/npm-version") NODEV=$(sed -n 2p "$S/npm/npm-version")
  [ -z "${SHIM:-}" ] || return 0
  serve "$NPORT" "$NPM_RUN/cache" "$NPM_RUN/shim.log" python3 "$S/npm/shim.py" "$NPORT" "$NPM_RUN/cache" --frozen ||
    return 1
  SHIM=$served; BG+=("$served"); trap 'kill "${BG[@]}" 2> /dev/null' EXIT
}

# pac reaches for curl only for a packument the snapshot lacks, and npm for
# git only for a git dependency: both fail here, as in scale.sh; and npm's
# HOME is setup.sh's, so no config of the host's reaches it
in_npm() {  # <command...>
  local p=$PATH h=$HOME
  export PATH=$NPM_RUN/bin:$PATH HOME=$NPM_RUN/home npm_config_git=false
  "$@"
  export PATH=$p HOME=$h
}

# the step's eco, set-up and variants, the tool last
step() {
  case $1 in
    debian) setup_debian && sets debian debian "" pac-tool pac-pubgrub apt ;;
    debian-cold) setup_debian &&
      sets debian-cold debian "repos/debian/Packages $RUN/aptroot $PAC $(store "$APT")" pac-tool pac-pubgrub apt ;;
    alpine) setup_alpine && sets alpine alpine "" pac-tool pac-pubgrub apk ;;
    opam) setup_opam && sets opam opam "" pac-tool pac-pubgrub opam ;;
    opam-cold) setup_opam &&
      sets opam-cold opam "repos/opam-repository $RUN/opamroot $PAC $(store opam)" pac-tool pac-pubgrub opam ;;
    cargo) setup_cargo && sets cargo cargo "" pac-tool pac-pubgrub cargo ;;
    npm|npm-shared|npm-placement) READING=${1#npm-}; setup_npm && in_npm sets "$1" npm "" pac-tool pac-pubgrub npm ;;
    *) return 2 ;;
  esac
}

oblock() {  # <step> <key> <query> <tool>
  local st=$1 k=$2 q=$3 tool=$4 dest r v
  dest="$RUN/res/$st/outliers/$k.csv"
  [ -s "$dest" ] && return 0
  mkdir -p "$RUN/res/$st/outliers" "$RUN/out/$st/outliers"
  quiet
  ROWS="$dest.tmp"; : > "$ROWS"
  for v in "$tool" pac-tool pac-pubgrub; do
    [ "$v" = "$tool" ] && measure "$st" "$k" "$q" "$v" 0 "$OCAP"
    for r in $(seq 1 "$OREPS"); do
      measure "$st" "$k" "$q" "$v" "$r" "$OCAP"
      [ "$(tail -n 1 "$ROWS" | awk -F, '{print $(NF - 2)}')" = 124 ] && { log "$q $v timed out at ${OCAP}s"; break; }
    done
  done
  mv "$ROWS" "$dest"
  log "$st/outliers $q done (load $(load1))"
}

run_outliers() {
  local st q k
  log "== outliers start: $(uptime)"
  SET=outliers
  while read -r st q <&3; do
    k=$(printf '%s\n' "$q" | python3 "$S/triage_lib.py" keys | cut -f1)
    case $st in
      '#'*|'') ;;
      debian) setup_debian && oblock "$st" "$k" "$q" apt ;;
      alpine) setup_alpine && oblock "$st" "$k" "$q" apk ;;
      opam) setup_opam && oblock "$st" "$k" "$q" opam ;;
      cargo) setup_cargo && oblock "$st" "$k" "$q" cargo ;;
      npm|npm-shared|npm-placement) READING=${st#npm-}; setup_npm && in_npm oblock "$st" "$k" "$q" npm ;;
      *) log "outliers: no step $st" ;;
    esac
  done 3< "$S/bench/outliers.txt"
  log "== outliers end: $(uptime)"
}

run_floor() {
  local dest="$RUN/res/floor/floor/true.csv" r
  [ -s "$dest" ] && return 0
  mkdir -p "$RUN/res/floor/floor" "$RUN/out/floor/floor"
  SET=floor ROWS="$dest.tmp"; : > "$ROWS"
  for r in $(seq 0 30); do
    run1 floor true time "$r" 0 "$RUN/out/floor/floor/true" "$(type -P true)"
    run1 floor true timeout+time "$r" 10 "$RUN/out/floor/floor/true" "$(type -P true)"
  done
  mv "$ROWS" "$dest"
}

run_info() {
  {
    echo "host: $(hostname)"; echo "date: $(date -u +%FT%TZ)"; uname -a
    lscpu | grep -E '^(Model name|Socket|Core|Thread|CPU\(s\)|CPU max|CPU min|NUMA node|Frequency boost)'
    free -g | head -n 2
    echo "governor: $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2> /dev/null)"
    echo "pac: $(sha256sum "$PAC")"
    echo "pin: ${PIN:-none}"
    echo "time: $GTIME ($("$GTIME" --version 2>&1 | head -n 1))"
    echo "apt: $("$APT" --version 2> /dev/null | head -n 1)"; echo "apk: $("${APK:-apk}" --version 2>&1)"
    echo "opam: $(opam --version)"; echo "cargo: $(cargo --version)"; echo "rustc: $(rustc --version)"
    echo "npm: $(npm --version) node: $(node --version)"; echo "python: $(python3 --version)"
    echo "ocamlc: $(command -v ocamlc || echo none)"
    echo "uptime: $(uptime)"
  } > "$RUN/machine.txt" 2>&1
  cat "$RUN/machine.txt"
}

for what in "$@"; do
  case $what in
    info) run_info ;;
    floor) run_floor ;;
    outliers) run_outliers ;;
    *) step "$what"; [ $? != 2 ] || { echo "bench.sh: unknown step $what" >&2; exit 2; } ;;
  esac
done
