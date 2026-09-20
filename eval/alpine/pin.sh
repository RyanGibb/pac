#!/usr/bin/env bash
# Re-run every goal that diverged in <base-tag>, with the provider apk
# chose named in our world as well.  A goal that then agrees exactly was
# a preference gap: apk's answer was already a resolution of our
# instance and only our ordering ranked it second.
# usage: pin.sh <exe> <base-tag> <tag>
set -u
S="$(cd "$(dirname "$0")" && pwd)"
exe=$1; base=$2; tag=$3
ok=0; bad=0
for g in $(cat "$S/goals.txt"); do
  [ -s "$S/out/$base/$g.oursonly" ] || [ -s "$S/out/$base/$g.apkonly" ] || continue
  ex=""
  for p in busybox-binsh icu-data-en openssh-client-default; do
    grep -qx "$p" "$S/apk-$g.names" && ex="$ex $p"
  done
  EXTRA="$ex" bash "$S/cmp.sh" "$exe" "$tag" "$g" > /dev/null
  if diff -q "$S/out/$tag/$g.ours" "$S/apk-$g.names" > /dev/null; then
    ok=$((ok+1))
  else
    bad=$((bad+1)); echo "still divergent: $g"; diff "$S/out/$tag/$g.ours" "$S/apk-$g.names"
  fi
done
printf 'PINNED now-exact=%d still-divergent=%d\n' "$ok" "$bad"
