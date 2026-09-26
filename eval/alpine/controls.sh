#!/usr/bin/env bash
# usage: controls.sh <scratch-dir>        APK as check.sh takes it
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
T=$(mkdir -p "$1" && cd "$1" && pwd)
APK="${APK:-apk}"
bad=0

st() {  # <name> <version> [field...]
  local c
  c=$(python3 -c 'import base64, hashlib, sys
print("Q1" + base64.b64encode(hashlib.sha1(sys.argv[1].encode()).digest()).decode())' "$1-$2")
  printf 'C:%s\nP:%s\nV:%s\nA:x86_64\nS:1\nI:1\nT:t\nU:u\nL:l\no:%s\nm:m\nt:1\n' \
    "$c" "$1" "$2" "$1"
  shift 2
  for f; do printf '%s\n' "$f"; done
  echo
}

# the expected verdicts as valid/minimal
run() {  # <dir> <index> <apkroot> <goal> <expected>
  local got
  got=$(APKROOT=$3 INDEX=$2 bash "$S/../check.sh" alpine "$1/ans.out" "$1/check" $4 |
    tail -n 1 | sed -n 's/.* valid=\([A-Z]*\) minimal=\(.*\)$/\1\/\2/p')
  printf '%-40s expect %-11s got %s\n' "$(basename "$1")" "$5" "$got"
  [ "$got" = "$5" ] || bad=1
}

answer() {  # <dir>, the "name version" rows on stdin
  sed 's/^/  /' > "$1/rows"
  { echo "packages ($(wc -l < "$1/rows")):"; cat "$1/rows"; } > "$1/ans.out"
}

# the index on stdin; the answer one "name version" per argument
ctl() {  # <name> <expected> <row>...
  local d=$T/$1 want=$2 goal=${GOAL:-a}; shift 2
  rm -rf "$d"; mkdir -p "$d"
  cat > "$d/APKINDEX"
  printf '%s\n' "$@" | answer "$d"
  if INDEX=$d/APKINDEX APK=$APK bash "$S/setup.sh" "$d/apkroot" > "$d/setup.log" 2>&1; then
    run "$d" "$d/APKINDEX" "$d/apkroot" "$goal" "$want"
  else
    printf '%-40s expect %-11s got SETUP\n' "$(basename "$d")" "$want"; bad=1
  fi
}

{ st a 1-r0 D:b; st b 1-r0; } | ctl f0-control VALID/yes 'a 1-r0' 'b 1-r0'
{ st a 1-r0 'D:b !v'; st b 1-r0 D:p; st p 1-r0 p:v; } |
  ctl f6-conflictvirt INVALID/- 'a 1-r0' 'b 1-r0' 'p 1-r0'
{ st a 1-r0 'D:b>=2'; st b 1-r0; } | ctl f8-version INVALID/- 'a 1-r0' 'b 1-r0'
# a bare provides without k: counts once its owner is named, and only then
{ st a 1-r0 D:v; st p 1-r0 p:v; } | ctl f9-virtnoprio INVALID/- 'a 1-r0' 'p 1-r0'
{ st a 1-r0 'D:v p'; st p 1-r0 p:v; } | ctl f11-virtnamed VALID/yes 'a 1-r0' 'p 1-r0'
{ st a 1-r0 D:v; st p 1-r0 p:v; } | GOAL='a p' ctl f12-virtquery VALID/yes 'a 1-r0' 'p 1-r0'

# a hard dependency that happens to carry i: is still hard
{ st a 1-r0 D:x; st x 1-r0 i:t; st t 1-r0; } | ctl f1-iifdep INVALID/- 'a 1-r0'
{ st a 1-r0; st y 1-r0 i:a; } | ctl f2-iifsoft INVALID/- 'a 1-r0'
{ st a 1-r0; st a 2-r0; } | ctl f4-dupver INVALID/- 'a 1-r0' 'a 2-r0'
{ st a 1-r0; st z 1-r0; } | ctl f10-junkrow INVALID/- 'a 1-r0' 'z 1-r0 extra'
# nothing needs z, but z's own dependency is still unmet
{ st a 1-r0; st z 1-r0 D:y; st y 1-r0; } | ctl f13-extrabroken INVALID/- 'a 1-r0' 'z 1-r0'

# consistent, but apk left to settle the query alone would change it:
# purging what nothing leads to, or swapping an unversioned provider for
# the higher priority
{ st a 1-r0; st b 1-r0 D:c; st c 1-r0 D:b; } |
  ctl f3-cycle VALID/no 'a 1-r0' 'b 1-r0' 'c 1-r0'
{ st a 1-r0 D:v; st p1 1-r0 p:v k:10; st p2 1-r0 p:v k:1; } |
  ctl f5-prio VALID/no 'a 1-r0' 'p2 1-r0'
{ st a 1-r0; st y 1-r0 'i:a t'; st t 1-r0; } | ctl f7-iifuntrig VALID/no 'a 1-r0' 'y 1-r0'

# apk failing for want of a root says nothing of the answer
d=$T/f14-noroot
rm -rf "$d"; mkdir -p "$d"
st a 1-r0 > "$d/APKINDEX"; echo 'a 1-r0' | answer "$d"
run "$d" "$d/APKINDEX" "$d/apkroot" a ERR/-

# apk's own answer less a package, or with more added: the added answer
# is one pac's PubGrub order gave, lua5.4 taken for lua beside lua5.2
INDEX=$S/../../repos/alpine/APKINDEX
if APK=$APK bash "$S/setup.sh" "$T/snap" > "$T/snap.log" 2>&1; then
  while IFS='|' read -r goal drop add want; do
    d=$T/snap-${goal// /_}-$drop-${add:--}
    rm -rf "$d"; mkdir -p "$d"
    for g in "$goal" $add; do
      "$APK" add --root "$T/snap/root" --usermode --allow-untrusted --no-network \
        --repository "$T/snap/repo" --simulate $g 2> /dev/null
    done | sed -n 's/^( *[0-9]*\/[0-9]*) Installing \([^ ]*\) (\(.*\))$/\1 \2/p' |
      awk -v x="$drop" '$1 != x && !seen[$0]++' | answer "$d"
    run "$d" "$INDEX" "$T/snap" "$goal" "$want"
  done <<'EOF'
git|-||VALID/yes
python3|-||VALID/yes
agetty-openrc|-||VALID/yes
lua lua5.2|-||VALID/yes
git|git-init-template||INVALID/-
python3|python3-pyc||INVALID/-
agetty-openrc|agetty-openrc||INVALID/-
lua lua5.2|-|lua5.4|VALID/no
EOF
else
  echo "snapshot controls: setup failed, see $T/snap.log"; bad=1
fi

exit $bad
