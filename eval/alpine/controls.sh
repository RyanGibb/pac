#!/usr/bin/env bash
# valid.sh's verdict on hand-written answers over hand-written indices,
# and on apk's own answers over the snapshot with one package taken out,
# beside the verdict each must get.  A check that passes every real answer
# says nothing until it is seen to fail these; the ones expected VALID keep
# it from failing everything.  Exits non-zero if any verdict differs.
# usage: controls.sh <scratch-dir>        APK as valid.sh takes it
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

run() {  # <dir> <index> <apkroot> <goal> <expected>
  local got
  got=$(APKROOT=$3 INDEX=$2 REPLAY=$1/ans \
    bash "$S/valid.sh" "$S/scale.sh" "$(realpath -m --relative-to="$S/out" "$1/out")" "$4" |
    awk '{print $NF}')
  printf '%-34s expect %-7s got %s\n' "$(basename "$1")" "$5" "$got"
  [ "$got" = "$5" ] || bad=1
}

answer() {  # <dir>, the "name version" rows on stdin
  { echo "packages (n):"; sed 's/^/  /'; echo "encoded solution: -"; } > "$1/ans.out"
  echo 0 > "$1/ans.rc"
}

# the index on stdin; the answer one "name version" per argument
ctl() {  # <name> <expected> <row>...
  local d=$T/$1 want=$2; shift 2
  rm -rf "$d"; mkdir -p "$d"
  cat > "$d/APKINDEX"
  printf '%s\n' "$@" | answer "$d"
  if INDEX=$d/APKINDEX APK=$APK bash "$S/setup.sh" "$d/apkroot" > "$d/setup.log" 2>&1; then
    run "$d" "$d/APKINDEX" "$d/apkroot" a "$want"
  else
    printf '%-34s expect %-7s got SETUP\n' "$1" "$want"; bad=1
  fi
}

{ st a 1-r0 D:b; st b 1-r0; } | ctl f0-control VALID 'a 1-r0' 'b 1-r0'
{ st a 1-r0; st b 1-r0 D:c; st c 1-r0 D:b; } |
  ctl f3-cycle INVALID 'a 1-r0' 'b 1-r0' 'c 1-r0'
# valid, but apk swaps an unversioned provider for the higher priority:
# too strict, and left so, since relaxing it changes the question
{ st a 1-r0 D:v; st p1 1-r0 p:v k:10; st p2 1-r0 p:v k:1; } |
  ctl f5-prio INVALID 'a 1-r0' 'p2 1-r0'
{ st a 1-r0 'D:b !v'; st b 1-r0 D:p; st p 1-r0 p:v; } |
  ctl f6-conflictvirt INVALID 'a 1-r0' 'b 1-r0' 'p 1-r0'
{ st a 1-r0; st y 1-r0 'i:a t'; st t 1-r0; } | ctl f7-iifuntrig INVALID 'a 1-r0' 'y 1-r0'
{ st a 1-r0 'D:b>=2'; st b 1-r0; } | ctl f8-version INVALID 'a 1-r0' 'b 1-r0'
{ st a 1-r0 D:v; st p 1-r0 p:v; } | ctl f9-virtnoprio INVALID 'a 1-r0' 'p 1-r0'

# a hard dependency that happens to carry i: is still hard
{ st a 1-r0 D:x; st x 1-r0 i:t; st t 1-r0; } | ctl f1-iifdep INVALID 'a 1-r0'
{ st a 1-r0; st y 1-r0 i:a; } | ctl f2-iifsoft INVALID 'a 1-r0'
{ st a 1-r0; st a 2-r0; } | ctl f4-dupver INVALID 'a 1-r0' 'a 2-r0'
{ st a 1-r0; st z 1-r0; } | ctl f10-junkrow INVALID 'a 1-r0' 'z 1-r0 extra'

# apk's own answer over the snapshot, whole and with one package out
INDEX=$S/../../repos/alpine/APKINDEX
if APK=$APK bash "$S/setup.sh" "$T/snap" > "$T/snap.log" 2>&1; then
  while read -r goal drop want; do
    d=$T/snap-$goal-$drop
    rm -rf "$d"; mkdir -p "$d"
    "$APK" add --root "$T/snap/root" --usermode --allow-untrusted --no-network \
      --repository "$T/snap/repo" --simulate "$goal" 2> /dev/null |
      sed -n 's/^( *[0-9]*\/[0-9]*) Installing \([^ ]*\) (\(.*\))$/\1 \2/p' |
      awk -v x="$drop" '$1 != x' | answer "$d"
    run "$d" "$INDEX" "$T/snap" "$goal" "$want"
  done <<'EOF'
git - VALID
python3 - VALID
agetty-openrc - VALID
git git-init-template INVALID
python3 python3-pyc INVALID
agetty-openrc agetty-openrc INVALID
EOF
else
  echo "snapshot controls: setup failed, see $T/snap.log"; bad=1
fi

exit $bad
