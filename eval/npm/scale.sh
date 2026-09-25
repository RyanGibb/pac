#!/usr/bin/env bash
# A query is closed when neither side asked for a name the snapshot lacks,
# tolerated-misses aside: only then are both answering about the snapshot.
# FILL=1 is the pass that closes a snapshot: the shim fetches each miss once
# into the run's farm, pac's fetches go through it, and what the farm gains
# is then copied into repos/npm by hand; a miss is then only a name the
# registry itself refuses.
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        MODES="default order=pubgrub" P=<jobs> TIMEOUT=<s> PORT=<shim>
#        NORM=<edges.py flag> FILL=1
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/../scale-lib.sh"
export PORT=${PORT:-8899} NORM=${NORM---peer-parent}
NPMV=$(sed -n 1p "$S/npm-version") NODEV=$(sed -n 2p "$S/npm-version")

all_queries() { node "$S/queries.js" "$TOP/repos/npm"; }

regress_queries() { awk '{print $1 "@" $2}' "$S/baseline/roots.txt"; }

prepare() {
  [ -n "${FILL:-}" ] || snapshot npm
  bash "$S/setup.sh" "$run" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  # pac fetches a missing packument with curl; this one records the name and
  # answers 404, or under FILL fetches it through the shim and records only
  # a refusal
  mkdir -p "$run/bin" "$run/work"
  if [ -n "${FILL:-}" ]; then
    printf '#!/bin/sh\nu=; o=\nwhile [ $# -gt 0 ]; do case $1 in -o) o=$2; shift;; https://*) u=$1;; esac; shift; done\n%s -fsS "http://127.0.0.1:%s/${u##*/}" -o "$o" && exit 0\necho "${u##*/}" >> "$PAC_MISS"; printf 404; exit 22\n' \
      "$(command -v curl)" "$PORT" > "$run/bin/curl"
  else
    printf '#!/bin/sh\nfor a; do case $a in https://*) echo "${a##*/}" >> "$PAC_MISS";; esac; done\nprintf 404; exit 22\n' \
      > "$run/bin/curl"
  fi
  # the shim fences the registry and nothing else, and npm clones a git
  # dependency itself, so npm's git records the repository and fails
  printf '#!/bin/sh\nfor a; do case $a in *://*) echo "$a" >> "$GIT_MISS";; esac; done\nexit 128\n' \
    > "$run/bin/git"
  chmod +x "$run/bin/curl" "$run/bin/git"
  local mode=--frozen
  [ -z "${FILL:-}" ] || mode=--fill
  python3 "$S/shim.py" "$PORT" "$run/cache" $mode &
  trap "kill $!" EXIT
  sleep 1
  # another run's shim on PORT would answer from its own farm
  kill -0 $! 2> /dev/null || { echo "$0: no shim on $PORT" >&2; return 1; }
}

npm_run() {  # <dir> <npm args...>
  (cd "$1" && shift && HOME=$run/home npm_config_git=$run/bin/git GIT_MISS=$o.gitmiss \
     timeout "$TIMEOUT" npm "$@" --loglevel=http \
     --registry "http://127.0.0.1:$PORT" --cache "$run/home/npmcache" \
     --userconfig "$run/home/.npmrc" --globalconfig "$run/home/npmrc-global" \
     --no-audit --no-fund --no-update-notifier)
}

ask() {  # <project dir>
  rm -f "$1/package-lock.json"
  npm_run "$1" install --package-lock-only > "$o.npm" 2>&1
  local rc=$?
  cp "$1/package-lock.json" "$o.theirs" 2>/dev/null || : > "$o.theirs"
  return $rc
}

npmc() { npm_run "$@"; }
. "$S/accepts.sh"

# pac's answer in one mode, under the stem <p>; the default mode keeps the
# query's own stem, where pin.sh and triage.py look
ask_pac() {  # <key> <mode> <p> <query words...>
  local k=$1 m=$2 p=$3 pac corr=- valid=- oo=- to=- t0 wall nodes=- edges=- n
  shift 3
  t0=$EPOCHREALTIME
  PATH=$run/bin:$PATH PAC_MISS=$o.pacmiss timeout "$TIMEOUT" "$run/pac.exe" npm $(flag "$m") \
    --cache "$run/cache" --tree --node-version "$NODEV" --npm-version "$NPMV" "$@" > "$p.out" 2>&1
  pac=$(pac_status $? "$p.out" '^node_modules (')
  wall=$(since "$t0")
  if [ "$pac" = ok ] && [ "$tool" = ok ]; then
    n=$(python3 "$S/edges.py" "$name" "$o.theirs" "$p.out" "$p" $NORM | sed 's/.*#//')
    oo=$(wc -l < "$p.nodes.oursonly") to=$(wc -l < "$p.nodes.npmonly")
    nodes=${n%,*,*,*} edges=${n#*,*,*,}
    echo "$n" | awk -F, '{exit !($1 == $2 && $2 == $3 && $4 == $5 && $5 == $6)}' && corr=exact || corr=diff
    [ -s "$p.edges.npmonly" ] && python3 "$S/verdict.py" "$run" "$name" "$p" "$w/lock/package.json" > /dev/null
  fi
  if [ "$pac" = ok ]; then
    if python3 "$S/mklock.py" "$run/cache" "$p.out" "$w/ci/package-lock.json" \
         --root-manifest "$w/ci/package.json" > "$p.mklock" 2>&1; then
      accepts "$w/ci" "$p" && valid=VALID || valid=INVALID
    else valid=ERR; fi
  fi
  echo "query=$k mode=$m pac=$pac tool=$tool corr=$corr valid=$valid oo=$oo to=$to wall=$wall twall=$twall closed=@closed@ nodes=$nodes edges=$edges"
}

one() {
  local o=$run/out/$1 w=$run/work/$1 name closed q m p lines=
  set -f; q=($2); set +f
  # roots.txt pins one version per name, so a one-spec query's recorded
  # lock is named for the name alone
  if [ ${#q[@]} -eq 1 ]; then name=${2:1}; name=${2:0:1}${name%%@*}; else name=$1; fi
  mkdir -p "$w/lock" "$w/ci"
  rm -f "$o.pacmiss" "$o.gitmiss" "$o.ci" "$o.plo"
  node "$S/root.js" "$run/cache" "${q[@]}" > "$w/lock/package.json" 2> "$o.root" || : > "$w/lock/package.json"
  cp "$w/lock/package.json" "$w/ci/package.json"
  answer "$S/baseline/lock-${name//\//__}" json ask "$w/lock"
  for m in $MODES; do
    p=$o; [ "$m" = default ] || p=$o.${m//=/-}
    lines+=$(ask_pac "$1" "$m" "$p" "${q[@]}")$'\n'
  done
  # a package npm resolved from anywhere but the registry came from outside
  # the snapshot, however it got past the fence, so it is a miss too
  { cat "$o.pacmiss" "$o.gitmiss" 2>/dev/null
    sed -n 's|^npm http fetch GET 404 http://[^/]*/\([^ ]*\) .*|\1|p' "$o.npm" "$o.ci" "$o.plo" 2>/dev/null
    jq -r '.packages[]?.resolved // empty' "$o.theirs" 2>/dev/null | grep -v '^https://registry\.npmjs\.org/'
  } | sed 's/%2[Ff]/\//g' | sort -u |
    grep -vxF -f <(sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/^$/d' "$S/tolerated-misses") > "$o.miss"
  [ -s "$o.miss" ] && closed=no || closed=yes
  printf '%s' "${lines//@closed@/$closed}"
}

totals() {
  awk '{for (i = 1; i <= NF; i++) {j = index($i, "="); f[substr($i, 1, j - 1)] = substr($i, j + 1)}
        c += f["closed"] == "yes"
        if (f["nodes"] != "-") {g++; split(f["nodes"] "," f["edges"], a, ","); for (i = 1; i <= 6; i++) t[i] += a[i]}
        if (f["twall"] != "-") {w++; pw += f["wall"]; nw += f["twall"]}}
    END {printf "closed %d/%d; over the %d both answer, nodes ours=%d npm=%d agree=%d, edges ours=%d npm=%d agree=%d\n",
           c, NR, g, t[1], t[2], t[3], t[4], t[5], t[6]
         if (w) printf "wall time over the %d queries npm was asked: pac %.1fs, npm %.1fs\n", w, pw, nw}' "$run/results.txt"
  find "$run/out" -name '*.verdict' -exec cut -f1 {} + | sort | uniq -c |
    sed 's/^ */npm-only edges: /'
}

main "$@"
