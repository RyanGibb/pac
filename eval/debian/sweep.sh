#!/usr/bin/env bash
# usage: sweep.sh <exe> <tag>               EXTRA=<flags> passes flags to <exe>
# Goals apt has no candidate for are tallied as absent, not as exact matches:
# the quotable denominator is the comparable count, not the goal count.
set -u
S="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$S/out"
exe=$1; tag=$2
for f in "$S"/apt-*.names; do
  g=$(basename "$f" .names); g=${g#apt-}
  echo "$g"
done | xargs -P 8 -I{} bash "$S/cmp.sh" "$exe" "$tag" {} > "$S/out/$tag.sweep" 2>&1
sort "$S/out/$tag.sweep" -o "$S/out/$tag.sweep"
awk '{if ($3=="absent") {ab++; next}
      oo=0;ao=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="ours-only")oo=a[2]; if(a[1]=="apt-only")ao=a[2]}
      if(oo==0&&ao==0) ex++; else {if(oo>0)oot+=oo; if(ao>0)aot+=ao; print}}
     END{printf "TOTAL exact=%d/%d absent=%d ours-only=%d apt-only=%d\n", ex, NR-ab, ab, oot, aot}' "$S/out/$tag.sweep"
