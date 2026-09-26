#!/usr/bin/env bash
# A query is closed when neither side asked for a name the snapshot lacks,
# tolerated-misses aside: only then are both answering about the snapshot.
# FILL=1 is the pass that closes a snapshot: the shim fetches each miss once
# into the run's farm, pac's fetches go through it, and what the farm gains
# is then copied into repos/npm by hand; a miss is then only a name the
# registry itself refuses.
# usage: scale.sh [--regress | --record] <pac-exe> <run-dir> [queries-file]
#        MODES="tool pubgrub" P=<jobs> TIMEOUT=<s> PORT=<shim>
#        NORM=<edges.py flag> FILL=1
S="$(cd "$(dirname "$0")" && pwd)"
ECO=npm
. "$S/../scale-lib.sh"
. "$S/npm.sh"
export PORT=${PORT:-8899} NORM=${NORM---peer-parent}
NPMV=$(sed -n 1p "$S/npm-version") NODEV=$(sed -n 2p "$S/npm-version")

all_queries() { node "$S/queries.js" "$TOP/repos/npm"; }

regress_queries() { awk '{print $1 "@" $2}' "$S/baseline/roots.txt"; }

params() { echo "NORM=$NORM"; echo "FILL=${FILL:-}"; }

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
  export NPM_RUN=$run NPM_GIT=$run/bin/git
  local mode=--frozen
  [ -z "${FILL:-}" ] || mode=--fill
  serve "$PORT" "$run/cache" "$run/shim.log" python3 "$S/shim.py" "$PORT" "$run/cache" $mode
}

refused() { grep -qE '^npm error code (ERESOLVE|ETARGET|E404|ENOVERSIONS|EBADPLATFORM)$' "$2"; }

ask() {  # <project dir>
  rm -f "$1/package-lock.json"
  GIT_MISS=$o.gitmiss NPM_TIMEOUT=$TIMEOUT npm_in "$1" install --package-lock-only --loglevel=http \
    > "$o.npm" 2>&1
  local rc=$?
  cp "$1/package-lock.json" "$o.theirs" 2>/dev/null || : > "$o.theirs"
  return $rc
}

# name is the package edges.py and verdict.py score, and w the query's
# work directory, both read by correspond
ask_tool() {
  local q
  q=($2); w=$run/work/$1
  # roots.txt pins one version per name, so a one-spec query's recorded
  # lock is named for the name alone
  if [ ${#q[@]} -eq 1 ]; then name=${2:1}; name=${2:0:1}${name%%@*}; else name=$1; fi
  mkdir -p "$w/lock"
  rm -f "$o.pacmiss" "$o.gitmiss"
  # npm is never asked a question other than the query's
  if node "$S/root.js" "$run/cache" "${q[@]}" > "$w/lock/package.json" 2> "$o.root" ||
     [ "$BASELINE" = regress ]; then
    answer "$S/baseline/lock-${name//\//__}" json "$o.npm" ask "$w/lock"
  else
    tool=error twall=-
  fi
}

run_pac() {
  rm -f "$2.counts"
  PATH=$run/bin:$PATH PAC_MISS=$o.pacmiss timeout "$TIMEOUT" "$run/pac.exe" npm $(flag "$1") \
    --cache "$run/cache" --tree --node-version "$NODEV" --npm-version "$NPMV" $3 > "$2.out" 2>&1
}

extract() { :; }

correspond() {
  local n
  n=$(python3 "$S/edges.py" "$name" "$o.theirs" "$1.out" "$1" $NORM | sed 's/.*#//')
  oo=$(wc -l < "$1.nodes.oursonly") to=$(wc -l < "$1.nodes.npmonly")
  echo "${n%,*,*,*} ${n#*,*,*,}" > "$1.counts"
  echo "$n" | awk -F, '{exit !($1 == $2 && $2 == $3 && $4 == $5 && $5 == $6)}' && corr=exact || corr=diff
  [ -s "$1.edges.npmonly" ] && python3 "$S/verdict.py" "$run" "$name" "$1" "$w/lock/package.json" > /dev/null
}

# answers are compared as trees, and every mode is checked
canon() { return 1; }

fields() {
  local c=(- -)
  [ -s "$1.counts" ] && read -r -a c < "$1.counts"
  printf ' twall=%s closed=@closed@ nodes=%s edges=%s' "$twall" "${c[0]}" "${c[1]}"
}

# a package npm resolved from anywhere but the registry came from outside
# the snapshot, however it got past the fence, so it is a miss too
emit() {
  local m closed
  { cat "$o.pacmiss" "$o.gitmiss" 2> /dev/null
    for m in $MODES; do cat "$o.$m.check/gitmiss" 2> /dev/null; done
    for m in $MODES; do
      sed -n 's|^npm http fetch GET 404 http://[^/]*/\([^ ]*\) .*|\1|p' \
        "$o.$m.check/ci.log" "$o.$m.check/plo.log" 2> /dev/null
    done
    sed -n 's|^npm http fetch GET 404 http://[^/]*/\([^ ]*\) .*|\1|p' "$o.npm" 2> /dev/null
    jq -r '.packages[]?.resolved // empty' "$o.theirs" 2>/dev/null | grep -v '^https://registry\.npmjs\.org/'
  } | sed 's/%2[Ff]/\//g' | sort -u |
    grep -vxF -f <(sed -e 's/#.*//' -e 's/[[:space:]]*$//' -e '/^$/d' "$S/tolerated-misses") > "$o.miss"
  [ -s "$o.miss" ] && closed=no || closed=yes
  printf '%s' "${1//@closed@/$closed}"
}

totals() {
  awk '{delete f; for (i = 1; i <= NF; i++) {j = index($i, "="); f[substr($i, 1, j - 1)] = substr($i, j + 1)}
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
