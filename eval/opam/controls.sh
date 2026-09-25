#!/usr/bin/env bash
# valid.sh's verdict on hand-written selections over a hand-written
# repository, beside the verdict each must get.  A check that passes every
# real answer says nothing until it is seen to fail these; the ones
# expected VALID keep it from failing everything.  Exits non-zero if any
# verdict differs.
# usage: controls.sh <scratch-dir>
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
T=$(mkdir -p "$1" && cd "$1" && pwd)
bad=0

R=$T/repo
rm -rf "$R"; mkdir -p "$R/packages"
echo 'opam-version: "2.0"' > "$R/repo"
pkg() {  # <name.version> [opam field...]
  local p=$R/packages/${1%%.*}/$1; shift
  mkdir -p "$p"
  { echo 'opam-version: "2.0"'; for f; do printf '%s\n' "$f"; done; } > "$p/opam"
}
pkg a.1; pkg a.2; pkg d.1; pkg e.1; pkg x.1; pkg y.1
pkg cc1.1 'conflict-class: "cc"'; pkg cc2.1 'conflict-class: "cc"'
pkg r.1 'depends: ["a"]'
pkg ro.1 'depopts: ["d"]'
pkg ro2.1 'depopts: ["d2"]'; pkg d2.1 'depends: ["e"]'
pkg dv.1 'depopts: ["a"]' 'conflicts: ["a" {>= "2"}]'
pkg ror.1 'depends: ["x" | "y"]'
pkg u.1 'available: false'; pkg uos.1 'available: os = "macos"'
pkg ru.1 'depends: ["u"]'; pkg ruo.1 'depends: ["uos"]'
pkg rcc.1 'depends: ["cc1" "cc2"]'
pkg ra.1 'depends: ["a" {< "2"}]'; pkg rb.1 'depends: ["a" {build & < "2"}]'
pkg rt.1 'depends: ["a" {with-test}]'; pkg rt2.1 'depends: ["a" {with-test} "x"]'
pkg rx.1 'conflicts: ["a"]'
pkg p.1 'depends: ["q" {post}]'; pkg q.1 'depends: ["p"]'
pkg p2.1 'depends: ["q2"]'; pkg q2.1 'depends: ["p2"]'
pkg pp.1 'depends: ["a" {post & < "2"}]'
pkg m1.1 'depends: ["m2"]'; pkg m2.1 'depends: ["m1"]'

if ! REPO=$R bash "$S/setup.sh" "$T/opamroot" > "$T/setup.log" 2>&1; then
  echo "setup failed, see $T/setup.log"; exit 1
fi

n=0
# an _ in a row stands for a space, so a row can carry a stray field
ctl() {  # <query> <selection> <expected>
  local d=$T/c$((n += 1)) got
  mkdir -p "$d"
  { echo "opam packages (n)"; printf '  %s\n' $2 | tr _ ' '; echo loaded; } > "$d/ans.out"
  echo 0 > "$d/ans.rc"
  got=$(OPAMROOT=$T/opamroot REPLAY=$d/ans \
    bash "$S/valid.sh" "$S/scale.sh" "$(realpath -m --relative-to="$S/out" "$d/out")" "$1" |
    awk '{print $NF}')
  printf '%-34s expect %-7s got %s\n' "[$1 | $2]" "$3" "$got"
  [ "$got" = "$3" ] || bad=1
}

ctl r 'r.1 a.1' VALID
ctl ror 'ror.1 x.1' VALID
ctl ror 'ror.1 y.1' VALID
ctl p 'p.1 q.1' VALID
ctl rb 'rb.1 a.1' VALID
ctl pp 'pp.1 a.1' VALID
ctl '--with-test rt' 'rt.1 a.1' VALID
ctl '--with-test rt2' 'rt2.1 x.1 a.1' VALID
ctl 'r ror' 'r.1 a.1 ror.1 x.1' VALID

ctl r 'r.1' INVALID
ctl r 'r.1 a.1 d.1' INVALID
ctl u 'u.1' INVALID
ctl uos 'uos.1' INVALID
ctl ru 'ru.1 u.1' INVALID
ctl ruo 'ruo.1 uos.1' INVALID
ctl rcc 'rcc.1 cc1.1 cc2.1' INVALID
ctl ra 'ra.1 a.2' INVALID
ctl rb 'rb.1 a.2' INVALID
ctl pp 'pp.1 a.2' INVALID
ctl rx 'rx.1 a.1' INVALID
ctl a 'a.9' INVALID
ctl a 'a.1 a.2' INVALID
ctl '--with-test rt' 'rt.1' INVALID
ctl rt 'rt.1 a.1' INVALID
ctl rt2 'rt2.1 x.1 a.1' INVALID
ctl r 'r.1 a.1 m1.1 m2.1' INVALID
ctl p2 'p2.1 q2.1' CYCLIC
ctl r 'r.1 a.1 y.1_extra' INVALID

# kept by `opam remove --auto-remove`, but nothing the roots need
ctl ro 'ro.1 d.1' INVALID
ctl ro2 'ro2.1 d2.1 e.1' INVALID
ctl dv 'dv.1 a.1' INVALID
ctl ror 'ror.1 x.1 y.1' INVALID

exit $bad
