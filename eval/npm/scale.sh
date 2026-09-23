#!/usr/bin/env bash
# cmp.sh's and valid.sh's questions over what a bare `npm install` of each
# packument in the snapshot installs, or over the name@spec goals a file
# lists (goals.js makes both), answered into the run directory against a
# frozen shim.  cmp.sh and valid.sh pin the
# root to roots.txt, so their steps are repeated here with the goal's own
# spec, which may be a range.
# A goal is closed when neither side asked for a name the snapshot lacks,
# tolerated-misses aside: only then are both answering about the snapshot.
# usage: scale.sh <pac-exe> <run-dir> [goals-file]    P=<jobs> TIMEOUT=<s> PORT=<shim>
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/../scale-lib.sh"
export PORT=${PORT:-8899}
NPMV=$(sed -n 1p "$S/npm-version") NODEV=$(sed -n 2p "$S/npm-version")

all_goals() { node "$S/goals.js" "$TOP/repos/npm"; }

prepare() {
  snapshot npm
  bash "$S/setup.sh" "$run" > "$run/setup.log" 2>&1 || { cat "$run/setup.log" >&2; return 1; }
  # pac fetches a missing packument with curl; this one records the name and fails
  mkdir -p "$run/bin" "$run/work"
  printf '#!/bin/sh\nfor a; do case $a in https://*) echo "${a##*/}" >> "$PAC_MISS";; esac; done\nexit 22\n' \
    > "$run/bin/curl"
  chmod +x "$run/bin/curl"
  python3 "$S/shim.py" "$PORT" "$run/cache" --frozen &
  trap "kill $!" EXIT
  sleep 1
}

npm_run() {  # <dir> <npm args...>
  (cd "$1" && shift && HOME=$run/home timeout "$TIMEOUT" npm "$@" --loglevel=http \
     --registry "http://127.0.0.1:$PORT" --cache "$run/home/npmcache" \
     --userconfig "$run/home/.npmrc" --globalconfig "$run/home/npmrc-global" \
     --no-audit --no-fund --no-update-notifier)
}

one() {
  local o=$run/out/$1 w=$run/work/$1 name=${2%@*} root pac tool corr=- valid=- oo=- to=- t0 wall n closed
  root=pac-root-$(printf %s "$1" | md5sum | cut -c1-16)
  mkdir -p "$w/lock" "$w/ci"
  rm -f "$w/lock/package-lock.json" "$o.pacmiss" "$o.ci"
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
  npm_run "$w/lock" install --package-lock-only > "$o.npm" 2>&1
  tool=$(tool_status $? "$w/lock/package-lock.json")
  if [ "$pac" = ok ] && [ "$tool" = ok ]; then
    n=$(python3 "$S/edges.py" "$name" "$w/lock/package-lock.json" "$o.out" "$o" --peer-parent |
        sed 's/.*#//')
    oo=$(wc -l < "$o.nodes.oursonly") to=$(wc -l < "$o.nodes.npmonly")
    echo "$n" | awk -F, '{exit !($1 == $2 && $2 == $3 && $4 == $5 && $5 == $6)}' && corr=exact || corr=diff
  fi
  if [ "$pac" = ok ]; then
    if python3 "$S/mklock.py" "$run/cache" "$o.out" "$w/ci/package-lock.json" \
         --root-manifest "$w/ci/package.json" > "$o.mklock" 2>&1; then
      npm_run "$w/ci" ci --dry-run > "$o.ci" 2>&1 && valid=VALID || valid=INVALID
    else valid=ERR; fi
  fi
  # npm reaches a git dependency past the shim, so that counts as a miss too
  { cat "$o.pacmiss" 2>/dev/null
    sed -n 's|^npm http fetch GET 404 http://[^/]*/\([^ ]*\) .*|\1|p' "$o.npm" "$o.ci" 2>/dev/null
    grep -o '"resolved": "git[^"]*' "$w/lock/package-lock.json" 2>/dev/null
  } | sed 's/%2[Ff]/\//g' | sort -u |
    grep -vxF -f <(sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/^$/d' "$S/tolerated-misses") > "$o.miss"
  [ -s "$o.miss" ] && closed=no || closed=yes
  echo "goal=$1 mode=default pac=$pac tool=$tool corr=$corr valid=$valid oo=$oo to=$to wall=$wall closed=$closed"
}

main "$@"
