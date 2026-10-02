#!/usr/bin/env bash
# Resolution time and memory: pac in each order against each ecosystem's
# own tool, asked what eval/<eco>/scale.sh asks and invoked as it invokes
# them, one measured process at a time; eval/README.md, Benchmarks.
# usage: bench.sh <step>...    step: info floor outliers, or
#          debian debian-ma alpine opam cargo npm npm-shared npm-placement,
#          each also as <step>-cold and <step>-first
# env: RUN (outside the source tree), PAC (default _build/default/bin/main.exe),
#      REPS (5), CAP (seconds, 0 for none), OREPS (3), OCAP (1800),
#      STRAT, SETS (regress strat), PIN (taskset -c 42), LOADSTART (2.5),
#      LOADMAX (3.5), PORT (cargo's proxy, 8991), NPORT (npm's shim, 8899),
#      DEPTH (placement's --depth, 8), PAC_CACHE (pac's cargo and debian
#      --cache in the warm steps, as run_query.py reads it; empty for
#      --no-cache, in every step), GTIME (GNU time), TEE
#      (/run/current-system/sw/bin/tee), FOREIGN (debian-ma's
#      <dir>/Packages.i386, as eval/SNAPSHOTS records it)
# Run inside `nix develop ./nix`, with no ocamlc on PATH: opam reads
# sys-ocaml-version off whatever ocamlc it finds.
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
TOP="$(cd "$S/.." && pwd)"
RUN="${RUN:?set RUN to a run directory outside the source tree}"
PAC=$(realpath "${PAC:-$TOP/_build/default/bin/main.exe}")
REPS="${REPS:-5}" CAP="${CAP:-0}" OREPS="${OREPS:-3}" OCAP="${OCAP:-1800}"
STRAT="${STRAT:-}" SETS="${SETS:-regress strat}" PIN="${PIN-taskset -c 42}"
LOADSTART="${LOADSTART:-2.5}" LOADMAX="${LOADMAX:-3.5}"
GTIME="${GTIME:-$(readlink -f /run/current-system/sw/bin/time)}"
APT="${APT:-apt-get}" DEPTH="${DEPTH:-8}" TEE="${TEE:-/run/current-system/sw/bin/tee}"
FOREIGN="${FOREIGN:-}" MODE=
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

# Each step supplies argv_<eco> <variant> <key> <query> <rep>, setting CMD
# and DIR, and may supply pre_<eco> <variant> <key> <query>, run untimed
# before each measured run; a variant pac-<order> is pac in that order, and
# rep 0 is the warm-up; <eco> is the step's name up to its first -
pre() {  # <step> <key> <query> <variant>
  local e=${1%%-*}
  ! declare -F "pre_$e" > /dev/null || "pre_$e" "$4" "$2" "$3" < /dev/null ||
    { log "$1 $3 $4: pre-step failed, not measured"; return 1; }
}
measure() {  # <step> <key> <query> <variant> <rep> <cap>
  local step=$1 k=$2 q=$3 v=$4 r=$5 cap=$6 e=${1%%-*} o
  [ "$r" = cold ] || pre "$step" "$k" "$q" "$v" || return 1
  "argv_$e" "$v" "$k" "$q" "$r"
  o="$RUN/out/$step/$SET/$k.$v"
  case $r in 0|1|cold) o="$o.$r" ;; *) o="$o.last" ;; esac
  pushd "$DIR" > /dev/null || return 1
  run1 "$step" "$q" "$v" "$r" "$cap" "$o" "${CMD[@]}"
  popd > /dev/null || return 1
}

order() { printf -- '--order=%s' "${1#pac-}"; }

# the set's queries as key<TAB>query, less the outliers of the step, or
# of the warm step a cold one is a mode of: the regression set of the eco
# the set is named for (debian's for debian-ma), or STRAT/<set>.q
queries() {  # <step> <set>
  local b=${1%-cold}
  b=${b%-first}
  case $SET in
    regress) if [ "${2%%-*}" = npm ]; then awk '{print $1 "@" $2}' "$S/npm/baseline/roots.txt"
             else cat "$S/${2%%-*}/queries.txt"; fi ;;
    strat) [ -z "$STRAT" ] || [ ! -e "$STRAT/$2.q" ] || awk -F'\t' '{print $NF}' "$STRAT/$2.q" ;;
  esac | python3 "$S/triage_lib.py" keys |
    awk -F'\t' 'FILENAME != "-" {out[$0]; next} !($2 in out)' <(sed -n "s/^$b //p" "$S/bench/outliers.txt") -
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

# A cold run starts with nothing in RAM: sync, then drop_caches, which
# drops the page cache and the dentry and inode caches alike, so a side
# that opens many small files pays for their directory entries as one
# reading a single cache file does not.  It is system-wide and needs root:
# the one command `sudo -n $TEE /proc/sys/vm/drop_caches`, TEE by full
# path as a sudoers rule names it.  drop.log keeps how long each took.
drop() {
  local t0=$EPOCHREALTIME
  sync && echo 3 | sudo -n "$TEE" /proc/sys/vm/drop_caches > /dev/null || return 1
  printf '%s %s\n' "$(date -u +%FT%TZ)" "$(elapsed "$t0" "$EPOCHREALTIME")" >> "$RUN/drop.log"
}
can_drop() {  # <step>
  sudo -n "$TEE" /proc/sys/vm/drop_caches < /dev/null > /dev/null 2>&1 && return 0
  log "$1: not run, a cold step needs 'sudo -n $TEE /proc/sys/vm/drop_caches', which sudo refuses"
  return 1
}

# One run per variant, in one of two modes, the same for both sides.
# cold: a cold start, both sides' persistent caches on disk and nothing in
# RAM; a run of the same command just before, rep 0, a warm-up the tables
# leave out, fills them with what this query reads.
# first: a first run, both sides' persistent caches deleted, as caches_<eco>
# lists them, so each parses from scratch and writes its cache.
cblock() {  # <step> <key> <query> <mode> <variant>...
  local step=$1 k=$2 q=$3 mode=$4 dest try v l
  shift 4
  dest="$RUN/res/$step/$SET/$k.csv"
  [ -s "$dest" ] && return 0
  mkdir -p "$RUN/res/$step/$SET" "$RUN/out/$step/$SET"
  for try in 1 2 3; do
    quiet
    ROWS="$dest.tmp"; : > "$ROWS"
    for v in "$@"; do
      if [ "$mode" = cold ]; then measure "$step" "$k" "$q" "$v" 0 "$CAP" || continue
      else rm -rf $("caches_${step%%-*}"); fi
      pre "$step" "$k" "$q" "$v" || continue
      drop || { log "$step $q $v: drop_caches failed, not measured"; continue; }
      measure "$step" "$k" "$q" "$v" cold "$CAP"
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

# each set of a step, every query a block, or in a mode a cold one; the
# mode is MODE's too, for an argv_ that asks otherwise in it
sets() {  # <step> <set> <mode or ""> <variant>...
  local step=$1 eco=$2 mode=$3 k q
  shift 3
  MODE=$mode
  [ -z "$mode" ] || can_drop "$step" || return 1
  log "== $step start${mode:+ ($mode, drop_caches)}: $(uptime)"
  for SET in $SETS; do
    while IFS=$'\t' read -r k q <&3; do
      if [ -n "$mode" ]; then cblock "$step" "$k" "$q" "$mode" "$@"; else block "$step" "$k" "$q" "$@"; fi
    done 3< <(queries "$step" "$eco")
  done
  log "== $step end: $(uptime)"
}

# pac's --cache, as apt reads its pkgcache.bin: the warm-up round fills
# it.  PAC_CACHE names another for the warm step; a cold step keeps its own.
caches_debian() {
  echo "$DCACHE" "$AROOT/var/cache/apt/pkgcache.bin" "$AROOT/var/cache/apt/srcpkgcache.bin"
}
argv_debian() {
  local cache=(--no-cache)
  DIR=$TOP
  [ -z "$DCACHE" ] || cache=(--cache "$DCACHE")
  case $1 in
    pac-*) CMD=("$PAC" debian $(order "$1") --native amd64 "${cache[@]}" "$DINDEX" $3) ;;
    apt) CMD=("$APT" -s install $3) ;;
  esac
}
setup_debian() {
  AROOT=$RUN/aptroot DINDEX=repos/debian/Packages
  [ -s "$AROOT/var/cache/apt/pkgcache.bin" ] ||
    FOREIGN= bash "$S/debian/setup.sh" "$AROOT" > "$RUN/apt-setup.log" 2>&1 ||
    { log "debian setup failed"; return 1; }
  export APT_CONFIG="$AROOT/etc/apt/apt.conf"
  DCACHE=${PAC_CACHE-$RUN/debian/pac-cache}
}
# the foreign index, checked against the row eval/SNAPSHOTS records for it
# as scale.sh checks it, and the two indexes as one file, made once so
# that pac's cache, which keys a file by its inode and times, holds
setup_debian_ma() {
  local id
  [ -s "$FOREIGN" ] || { log "debian-ma: FOREIGN names no foreign index"; return 1; }
  id=$(sha256sum < "$FOREIGN" | cut -d' ' -f1)
  grep -q "^ *foreign/debian/${FOREIGN##*/} *$id " "$S/SNAPSHOTS" ||
    { log "debian-ma: $FOREIGN is $id, not what eval/SNAPSHOTS records"; return 1; }
  AROOT=$RUN/aptroot-ma DINDEX=$RUN/debian-ma/Packages
  if [ ! -s "$DINDEX" ]; then
    mkdir -p "$RUN/debian-ma"
    cat repos/debian/Packages "$FOREIGN" > "$DINDEX.new" && mv "$DINDEX.new" "$DINDEX" || return 1
  fi
  [ -s "$AROOT/var/cache/apt/pkgcache.bin" ] ||
    FOREIGN=$FOREIGN bash "$S/debian/setup.sh" "$AROOT" > "$RUN/apt-setup-ma.log" 2>&1 ||
    { log "debian-ma setup failed"; return 1; }
  export APT_CONFIG="$AROOT/etc/apt/apt.conf"
  DCACHE=${PAC_CACHE-$RUN/debian-ma/pac-cache}
}

argv_alpine() {
  DIR=$TOP
  case $1 in
    pac-*) CMD=("$PAC" alpine $(order "$1") repos/alpine/APKINDEX $3) ;;
    apk) CMD=("$APK" add --root "$RUN/apkroot/root" --usermode --allow-untrusted
              --no-network --repository "$RUN/apkroot/repo" --simulate $3) ;;
  esac
}
# neither side keeps one: apk re-reads APKINDEX.tar.gz each run, and its
# root's var/cache/apk stays empty, so a first run is a cold start
caches_alpine() { :; }
setup_alpine() {
  [ -s "$RUN/apkroot/repo/x86_64/APKINDEX.tar.gz" ] ||
    bash "$S/alpine/setup.sh" "$RUN/apkroot" > "$RUN/apk-setup.log" 2>&1 ||
    { log "alpine setup failed"; return 1; }
  APK=$(sed -n 's/^export APK=//p' "$RUN/apk-setup.log")
}

argv_opam() {
  DIR=$TOP
  case $1 in
    pac-*) CMD=("$PAC" opam --opam-version "$OV" --environment "$PLAT" $(order "$1") repos/opam-repository $3) ;;
    opam) CMD=(opam install $3 --dry-run --solver=builtin-0install --switch cmp --no-depexts -y) ;;
    # opam's default solver, an optimising one, timed beside the one pac
    # is compared with
    opam-mccs) CMD=(opam install $3 --dry-run --solver=builtin-mccs+glpk --switch cmp --no-depexts -y) ;;
  esac
}
# pac keeps no cache for opam; opam, its repository state marshalled
caches_opam() { echo "$OPAMROOT"/repo/state-*.cache; }
setup_opam() {
  if command -v ocamlc > /dev/null; then
    log "ocamlc on PATH ($(command -v ocamlc)): opam would read sys-ocaml-version from it"
    return 1
  fi
  export OPAMROOT="$RUN/opamroot"
  [ -d "$OPAMROOT/cmp" ] || bash "$S/opam/setup.sh" "$OPAMROOT" > "$RUN/opam-setup.log" 2>&1 ||
    { log "opam setup failed"; return 1; }
  OV=$(opam --version)
  PLAT=$(. "$S/opam/platform.sh" && root_platform) || { log "$OPAMROOT holds no platform"; return 1; }
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
# pac's and, under CARGO_HOME, cargo's copy of the index entries it fetched
caches_cargo() { echo "${PCACHE[1]:-}" "$CARGO_HOME/registry/index"; }
argv_cargo() {
  DIR=$TOP
  case $1 in
    pac-*) CMD=("$PAC" cargo "$TOP/repos/crates.io-index" "$CARGO_CMP_OUT/work/$3/Cargo.toml"
                --rust-version "$RUSTV" --print-parents $(order "$1")
                "${PCACHE[@]}") ;;
    cargo) CMD=(cargo generate-lockfile --manifest-path "$CARGO_CMP_OUT/work/$3/Cargo.toml") ;;
  esac
}
setup_cargo() {
  export CARGO_CMP_OUT=$RUN/cargo CARGO_HOME=$RUN/cargo/cargo-home
  PCACHE=(--cache "${PAC_CACHE-$CARGO_CMP_OUT/pac-cache}")
  [ -n "${PCACHE[1]}" ] || PCACHE=(--no-cache)
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
  local more=(--tree)
  DIR=$TOP
  [ "$READING" != placement ] || more=(--depth "$DEPTH")
  case $1 in
    pac-*)
      CMD=("$PAC" npm $(order "$1") --reading="$READING" "${more[@]}" --cache "$NPM_RUN/cache"
           --node-version "$NODEV" --npm-version "$NPMV" $3) ;;
    npm)
      DIR=$NPM_RUN/work/$2
      CMD=(npm install --package-lock-only --loglevel=http --registry "http://127.0.0.1:$NPORT"
           --cache "$NCACHE" --userconfig "$NPM_RUN/home/.npmrc"
           --globalconfig "$NPM_RUN/home/npmrc-global" --no-audit --no-fund --no-update-notifier)
      # the warm-up fills npm's cache from the shim; a measured round then
      # reads that cache alone, as pac reads the snapshot from disk.  A
      # first run has no cache to read, so it asks the shim
      [ "$4" = 0 ] || [ "$MODE" = first ] || CMD+=(--offline) ;;
  esac
}
# npm's cache; pac's --cache is the snapshot itself, which it only reads
caches_npm() { echo "$NCACHE"; }
setup_npm() {
  NPM_RUN=$RUN/npm NCACHE=$RUN/npm/home/npmcache
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

# the step's set-up, its query set and its variants, the tool last (opam:
# then builtin-mccs); a cold step keeps its own caches, pac's and, for npm,
# the tool's, in $RUN/<step>, so a warm step's are never touched
step() {
  local base=${1%-cold} mode=
  base=${base%-first}
  [ "$base" = "$1" ] || mode=${1##*-}
  case $base in
    debian|debian-ma)
      if [ "$base" = debian ]; then setup_debian; else setup_debian_ma; fi || return 1
      [ -z "$mode" ] || DCACHE=${DCACHE:+$RUN/$1/pac-cache}
      sets "$1" "$base" "$mode" pac-tool pac-pubgrub apt ;;
    alpine) setup_alpine && sets "$1" alpine "$mode" pac-tool pac-pubgrub apk ;;
    opam) setup_opam && sets "$1" opam "$mode" pac-tool pac-pubgrub opam opam-mccs ;;
    cargo) setup_cargo || return 1
      [ -z "$mode" ] || [ "${PCACHE[0]}" = --no-cache ] || PCACHE=(--cache "$RUN/$1/pac-cache")
      sets "$1" cargo "$mode" pac-tool pac-pubgrub cargo ;;
    npm|npm-shared|npm-placement) READING=${base#npm-}; setup_npm || return 1
      [ -z "$mode" ] || NCACHE=$RUN/$1/npmcache
      in_npm sets "$1" npm "$mode" pac-tool pac-pubgrub npm ;;
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
  SET=outliers MODE=
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
    [ -z "$FOREIGN" ] || echo "foreign: $(sha256sum "$FOREIGN")"
    echo "pin: ${PIN:-none}"
    echo "drop_caches: $(sudo -n "$TEE" /proc/sys/vm/drop_caches < /dev/null > /dev/null 2>&1 && echo allowed || echo refused)"
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
