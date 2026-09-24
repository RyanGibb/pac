#!/usr/bin/env bash
# Whether pac resolves as npm install --package-lock-only does, on nodes and
# on edges, and whether npm ci accepts pac's answer, over what a bare `npm
# install` of each packument in the snapshot installs, or over the
# name@spec goals a file lists (goals.js makes both), answered into the run
# directory against a frozen shim.  The regression set is baseline/roots.txt,
# each goal pinned to the version seed.sh chose for it.
# A goal is closed when neither side asked for a name the snapshot lacks,
# tolerated-misses aside: only then are both answering about the snapshot.
# FILL=1 is the pass that closes a snapshot: the shim fetches each miss once
# into the run's farm, pac's fetches go through it, and what the farm gains
# is copied into repos/npm afterwards; a miss is then only a name the
# registry itself refuses.
# NORM is edges.py's normalisation of npm's edges; NORM= scores them raw.
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [goals-file]
#        P=<jobs> TIMEOUT=<s> PORT=<shim> NORM=<edges.py flag> FILL=1
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/../scale-lib.sh"
export PORT=${PORT:-8899} NORM=${NORM---peer-parent}
NPMV=$(sed -n 1p "$S/npm-version") NODEV=$(sed -n 2p "$S/npm-version")

all_goals() { node "$S/goals.js" "$TOP/repos/npm"; }

regress_goals() { awk '{print $1 "@" $2}' "$S/baseline/roots.txt"; }

prepare() {
  [ -n "${FILL:-}" ] || snapshot npm
  bash "$S/setup.sh" "$run" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  # pac fetches a missing packument with curl; this one records the name and
  # fails, or under FILL fetches it through the shim and records only a refusal
  mkdir -p "$run/bin" "$run/work"
  if [ -n "${FILL:-}" ]; then
    printf '#!/bin/sh\nu=; o=\nwhile [ $# -gt 0 ]; do case $1 in -o) o=$2; shift;; https://*) u=$1;; esac; shift; done\n%s -fsS "http://127.0.0.1:%s/${u##*/}" -o "$o" && exit 0\necho "${u##*/}" >> "$PAC_MISS"; exit 22\n' \
      "$(command -v curl)" "$PORT" > "$run/bin/curl"
  else
    printf '#!/bin/sh\nfor a; do case $a in https://*) echo "${a##*/}" >> "$PAC_MISS";; esac; done\nexit 22\n' \
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

one() {
  local o=$run/out/$1 w=$run/work/$1 name=${2%@*} root pac tool corr=- valid=- oo=- to=- t0 wall
  local nodes=- edges=- closed n
  # a recorded lock names its root, and roots.txt pins one version per
  # name, so a baseline's root is named for the name alone, as mkroot.py
  # names valid.sh's
  if [ -n "$BASELINE" ]; then root=${name//@/}; root=pac-root-${root//\//-}
  else root=pac-root-$(printf %s "$1" | md5sum | cut -c1-16); fi
  mkdir -p "$w/lock" "$w/ci"
  rm -f "$o.pacmiss" "$o.gitmiss" "$o.ci" "$run/cache/$root.json"
  jq -n --arg r "$root" --arg n "$name" --arg s "${2##*@}" \
    '{name: $r, version: "1.0.0", private: true, dependencies: {($n): $s}}' > "$w/lock/package.json"
  cp "$w/lock/package.json" "$w/ci/package.json"
  jq '{name, "dist-tags": {latest: "1.0.0"}, versions: {"1.0.0": .}}' "$w/lock/package.json" \
    > "$run/cache/$root.json"
  t0=$EPOCHREALTIME
  PATH=$run/bin:$PATH PAC_MISS=$o.pacmiss timeout "$TIMEOUT" "$run/pac.exe" npm --cache "$run/cache" \
    --tree --node-version "$NODEV" --npm-version "$NPMV" "$root" > "$o.out" 2>&1
  pac=$(pac_status $? "$o.out" '^node_modules (')
  wall=$(since "$t0")
  answer "$S/baseline/lock-${name//\//__}" json ask "$w/lock"
  if [ "$pac" = ok ] && [ "$tool" = ok ]; then
    n=$(python3 "$S/edges.py" "$name" "$o.theirs" "$o.out" "$o" $NORM | sed 's/.*#//')
    oo=$(wc -l < "$o.nodes.oursonly") to=$(wc -l < "$o.nodes.npmonly")
    nodes=${n%,*,*,*} edges=${n#*,*,*,}
    echo "$n" | awk -F, '{exit !($1 == $2 && $2 == $3 && $4 == $5 && $5 == $6)}' && corr=exact || corr=diff
    [ -s "$o.edges.npmonly" ] && python3 "$S/verdict.py" "$run" "$name" "$o" > /dev/null
  fi
  if [ "$pac" = ok ]; then
    if python3 "$S/mklock.py" "$run/cache" "$o.out" "$w/ci/package-lock.json" \
         --root-manifest "$w/ci/package.json" > "$o.mklock" 2>&1; then
      npm_run "$w/ci" ci --dry-run > "$o.ci" 2>&1 && valid=VALID || valid=INVALID
    else valid=ERR; fi
  fi
  # a package npm resolved from anywhere but the registry came from outside
  # the snapshot, however it got past the fence, so it is a miss too
  { cat "$o.pacmiss" "$o.gitmiss" 2>/dev/null
    sed -n 's|^npm http fetch GET 404 http://[^/]*/\([^ ]*\) .*|\1|p' "$o.npm" "$o.ci" 2>/dev/null
    jq -r '.packages[]?.resolved // empty' "$o.theirs" 2>/dev/null | grep -v '^https://registry\.npmjs\.org/'
  } | sed 's/%2[Ff]/\//g' | sort -u |
    grep -vxF -f <(sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/^$/d' "$S/tolerated-misses") > "$o.miss"
  [ -s "$o.miss" ] && closed=no || closed=yes
  echo "goal=$1 mode=default pac=$pac tool=$tool corr=$corr valid=$valid oo=$oo to=$to wall=$wall twall=$twall closed=$closed nodes=$nodes edges=$edges"
}

totals() {
  awk '{for (i = 1; i <= NF; i++) {j = index($i, "="); f[substr($i, 1, j - 1)] = substr($i, j + 1)}
        c += f["closed"] == "yes"
        if (f["nodes"] != "-") {g++; split(f["nodes"] "," f["edges"], a, ","); for (i = 1; i <= 6; i++) t[i] += a[i]}
        if (f["twall"] != "-") {w++; pw += f["wall"]; nw += f["twall"]}}
    END {printf "closed %d/%d; over the %d both answer, nodes ours=%d npm=%d agree=%d, edges ours=%d npm=%d agree=%d\n",
           c, NR, g, t[1], t[2], t[3], t[4], t[5], t[6]
         if (w) printf "wall time over the %d goals npm was asked: pac %.1fs, npm %.1fs\n", w, pw, nw}' "$run/results.txt"
  find "$run/out" -name '*.verdict' -exec cut -f1 {} + | sort | uniq -c |
    sed 's/^ */npm-only edges: /'
}

main "$@"
