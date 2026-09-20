#!/usr/bin/env bash
# usage: sweep.sh <exe> <tag>
set -u
S="$(cd "$(dirname "$0")" && pwd)"
exe=$1; tag=$2
mkdir -p "$S/out"
xargs -P 4 -I{} bash "$S/cmp.sh" "$exe" "$tag" {} < "$S/goals.txt" > "$S/out/$tag.sweep" 2>&1
sort "$S/out/$tag.sweep" -o "$S/out/$tag.sweep"
awk '{oo=0;to=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="ours-only")oo=a[2]; if(a[1]=="0i-only")to=a[2]}
      if(oo==0&&to==0) ex++; else {oot+=oo; tot+=to; print}}
     END{printf "TOTAL exact=%d ours-only=%d 0i-only=%d\n", ex, oot, tot}' "$S/out/$tag.sweep"
