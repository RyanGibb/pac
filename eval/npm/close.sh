#!/usr/bin/env bash
# Closes repos/npm over every query a sweep asks -- the names queries.js
# lists, its targeted ranges and the regression set -- in each reading and
# both orders, for the pac given: a FILL=1 scale.sh pass per reading, the
# three at once, then what their farms fetched copied into repos/npm, until
# a pass fetches nothing.  It is the one thing meant to write into
# repos/npm, so rerun it whenever pac changes, and record the hash it ends
# with in eval/SNAPSHOTS.  A killed run resumes: rerun the same line.
#
# It ends with the names the last pass still missed, which no fill can
# fetch: the registry refuses them, or they are git repositories.
#
# usage: close.sh <pac-exe> <work-dir>
#        PORT=<the first of three shim ports> P=<jobs per reading> TIMEOUT=<s>
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
[ $# -eq 2 ] || { echo "usage: $0 <pac-exe> <work-dir>" >&2; exit 2; }
SNAP=$(realpath "$S/../../repos/npm") || exit 1
exe=$(realpath "$1") || exit 1
mkdir -p "$2" && W=$(cd "$2" && pwd) || exit 1
PORT=${PORT:-8899}
export P=${P:-$(( $(nproc) / 3 ))}
READINGS="npm shared placement"

if [ ! -s "$W/queries.txt" ]; then
  { node "$S/queries.js" "$SNAP" && node "$S/queries.js" "$SNAP" targeted &&
      awk '{print $1 "@" $2}' "$S/baseline/roots.txt"; } > "$W/queries.new" &&
    mv "$W/queries.new" "$W/queries.txt" || exit 1
fi

# a farm's fetches are its regular files, the snapshot being symlinks
merge() {  # <run-dir>: prints how many files repos/npm gained
  local f n=0
  mkdir -p "$SNAP/tarballs"
  while IFS= read -r f; do
    [ -e "$SNAP/$f" ] && continue
    cp -p "$1/cache/$f" "$SNAP/.$f.tmp" && mv "$SNAP/.$f.tmp" "$SNAP/$f" && n=$((n + 1))
  done < <(cd "$1/cache" && find . -maxdepth 1 -type f -name '*.json' -printf '%P\n')
  while IFS= read -r f; do
    [ -e "$SNAP/tarballs/$f" ] && continue
    cp -p "$1/tarballs/$f" "$SNAP/tarballs/.$f.tmp" && mv "$SNAP/tarballs/.$f.tmp" "$SNAP/tarballs/$f" &&
      n=$((n + 1))
  done < <(cd "$1/tarballs" && find . -maxdepth 1 -type f -name '*.tgz' -printf '%P\n')
  echo "$n"
}

n=1
while :; do
  if [ ! -e "$W/pass$n.gained" ]; then
    i=0 pids=()
    for r in $READINGS; do
      FILL=1 READING=$r PORT=$((PORT + i)) bash "$S/scale.sh" "$exe" "$W/pass$n-$r" "$W/queries.txt" \
        > "$W/pass$n-$r.log" 2>&1 &
      pids+=($!); i=$((i + 1))
    done
    bad=0
    for i in "${!pids[@]}"; do wait "${pids[$i]}" || bad=1; done
    g=0
    for r in $READINGS; do g=$((g + $(merge "$W/pass$n-$r"))); done
    # a pass whose workers died may have left fetches undone, so it counts
    # as no pass: a rerun resumes it
    [ "$bad" = 0 ] || { echo "$0: a reading of pass $n failed (see $W/pass$n-*.log); rerun to resume" >&2; exit 1; }
    echo "$g" > "$W/pass$n.gained"
  fi
  echo "pass $n: repos/npm gained $(cat "$W/pass$n.gained") files"
  [ "$(cat "$W/pass$n.gained")" != 0 ] || break
  n=$((n + 1))
done

for r in $READINGS; do
  echo "$r: not closed $(awk '/ mode=tool / && / closed=no /' "$W/pass$n-$r/results.txt" | wc -l)" \
    "of $(awk '/ mode=tool /' "$W/pass$n-$r/results.txt" | wc -l) queries"
done
echo "still missing, the registry's refusals and git repositories:"
cat "$W"/pass$n-*/out/*.miss 2> /dev/null | sort | uniq -c
echo "repos/npm: $(find "$SNAP" -maxdepth 1 -type f -name '*.json' | wc -l) packuments," \
  "$(find "$SNAP/tarballs" -type f -name '*.tgz' | wc -l) tarballs, $(du -sh "$SNAP" | cut -f1)"
echo "repos/npm $(cd "$SNAP" && find . -type f -printf '%P\n' | sort | tr '\n' '\0' |
  xargs -0 sha256sum | awk '{print $1}' | sort | sha256sum | cut -d' ' -f1)"
