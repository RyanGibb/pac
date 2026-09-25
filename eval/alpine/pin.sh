#!/usr/bin/env bash
# Of a run's divergent queries, those pac answers exactly as apk does once
# every package of apk's answer is in the world: scale.sh's pin_tool asked
# that of each query apk answered, into out/<key>.pin.  A query still
# divergent is a gap of the instance or of pac, not of preference.
# usage: pin.sh <run-dir>
set -u
export LC_ALL=C
run=$1
ok=0; bad=0
for k in $(sed -n 's/^query=\([^ ]*\) .* corr=diff .*/\1/p' "$run/results.txt" | sort -u); do
  o=$run/out/$k
  if [ -e "$o.pin" ] && cmp -s "$o.pin" "$o.theirs"; then
    ok=$((ok+1))
  else
    bad=$((bad+1)); echo "still divergent: $k"
    diff "$o.pin" "$o.theirs" 2>&1
  fi
done
printf 'PINNED now-exact=%d still-divergent=%d\n' "$ok" "$bad"
