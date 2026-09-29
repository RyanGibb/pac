# Sourced by check.sh and layout-check.sh, each with its verdict <valid>
# <why> defined, and their arguments: <answer> <out-dir> <query...>.  The
# query's package.json goes in a fresh W, and npmc runs npm as both run it.
# NPM_RUN holds the snapshot farm (cache/) and a scratch home/, as setup.sh
# builds them; PORT is where shim.py serves that farm; NPM_GIT names the
# git npm is to run (default: none).
set -u
# byte order, so the output is the same whatever the host's locale
export LC_ALL=C
RUN=${NPM_RUN:?} PORT=${PORT:-8899}
ans=$1 out=$2; shift 2
W=$out/ci
. "$S/npm.sh"
. "$S/refused.sh"
npmc() { GIT_MISS=$out/gitmiss NPM_TIMEOUT= npm_in "$@" --loglevel=http; }  # <dir> <npm args...>
shim() { curl -s -o /dev/null "http://127.0.0.1:$PORT/-/ping"; }
err=0
ran() {  # <rc> <log>: whether npm ran to an answer, a refusal included
  [ "$1" -eq 0 ] || refused "$1" "$2" || err=1
}
problems() {  # npm ls's invalid and missing edges in W, counted in broken
  npmc "$W" ls --all --package-lock-only --json > "$out/ls.json" 2> "$out/ls.log" ||
    grep -q ELSPROBLEMS "$out/ls.log" || err=1
  jq -r '.problems[]? | select(startswith("invalid:") or startswith("missing:"))' \
    "$out/ls.json" > "$out/ls.problems" 2>&1 || err=1
  broken=$(wc -l < "$out/ls.problems")
}

rm -rf "$W" "$W.plo"; mkdir -p "$W"
shim || verdict ERR "no shim on $PORT"
if [ $# -eq 1 ] && [ "${1##*/}" = package.json ] && [ -f "$1" ]; then
  cp "$1" "$W/package.json"
else
  node "$S/root.js" "$RUN/cache" "$@" > "$W/package.json" 2> "$out/root.log" ||
    verdict ERR "root.js failed"
fi
