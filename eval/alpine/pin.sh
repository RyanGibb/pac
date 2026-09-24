#!/usr/bin/env bash
# Re-ask pac every query of a scale.sh run that diverged from apk, with the
# provider apk chose named in our world as well.  A query that then agrees
# exactly was a preference gap: apk's answer was already a resolution of
# our instance and only our ordering ranked it second.
# usage: pin.sh <run-dir>
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
run=$1
ok=0; bad=0
set -f
for k in $(sed -n 's/^query=\([^ ]*\) .* corr=diff .*/\1/p' "$run/results.txt"); do
  g=${k//+/ }; g=${g//%2F//}; g=${g//%2B/+}; g=${g//%25/%}
  o=$run/out/$k
  ex=""
  for p in busybox-binsh icu-data-en openssh-client-default; do
    grep -qx "$p" "$o.theirs" && ex="$ex $p"
  done
  "$run/pac.exe" alpine "$S/../../repos/alpine/APKINDEX" $g $ex > "$o.pin.out" 2>&1
  sed -n '/^packages (/,/^encoded solution/s/^  \([^ ]*\) .*/\1/p' "$o.pin.out" | sort -u > "$o.pin"
  if cmp -s "$o.pin" "$o.theirs"; then
    ok=$((ok+1))
  else
    bad=$((bad+1)); echo "still divergent: $g"; diff "$o.pin" "$o.theirs"
  fi
done
printf 'PINNED now-exact=%d still-divergent=%d\n' "$ok" "$bad"
