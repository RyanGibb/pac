#!/usr/bin/env bash
# How often pac's answer is builtin-mccs+glpk's, opam's default solver,
# over a finished scale.sh run: divergence from an optimising solver, not
# correspondence, which is 0install's.  Each query is asked as scale.sh
# asks 0install, with the run's OPAMROOT, one copy per worker (opam holds
# the switch's lock for a whole dry run).
# --accept <n> <seed> then asks 0install, for n of the queries where mccs
# and pac differ in the tool's order, drawn seeded, whether it takes mccs's
# answer as it stands.
# Writes <run-dir>/mccs.txt, a line per query:
#   query=<key> mccs=ok|refuse|error|timeout tool=<mode>:exact|diff ...
# and with --accept, <run-dir>/mccs-accept.txt:
#   query=<key> accepted=yes|no|error
# usage: mccs.sh [--accept <n> <seed>] <run-dir>    P=<jobs> TIMEOUT=<s>
#        inside nix develop ./nix, with no ocamlc on PATH, as scale.sh
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/../answer.sh"
. "$S/refused.sh"
P=${P:-$(nproc)} TIMEOUT=${TIMEOUT:-900}
acc=
if [ "${1:-}" = --accept ]; then acc=$2 seed=$3; shift 3; fi
run=$(cd "${1:?usage: mccs.sh [--accept <n> <seed>] <run-dir>}" && pwd) || exit 1
[ -d "$run/opamroot" ] && [ -s "$run/results.txt" ] || { echo "$0: $run is no finished opam run" >&2; exit 1; }
if command -v ocamlc > /dev/null; then echo "$0: ocamlc is on PATH" >&2; exit 1; fi
M=$run/mccs
mkdir -p "$M/out"

# <slot> <key> <query words>: mccs's answer into out/<key>.sel, and its line
one() {
  local slot=$1 k=$2 o=$M/out/$2 rc st m line; shift 2
  OPAMROOT=$M/root.$slot timeout "$TIMEOUT" opam install "$@" --dry-run --solver=builtin-mccs+glpk \
    --switch cmp --no-depexts -y > "$o.log" 2>&1
  rc=$?
  sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$o.log" | sort -u > "$o.sel"
  if [ "$rc" -eq 124 ]; then st=timeout
  elif [ "$rc" -eq 0 ] && [ -s "$o.sel" ]; then st=ok
  elif [ "$rc" -ne 0 ] && refused "$rc" "$o.log"; then st=refuse
  else st=error; fi
  line="query=$k mccs=$st"
  for m in tool pubgrub; do
    if [ "$st" = ok ] && [ -e "$run/out/$k.$m.out" ] && grep -q '^packages (' "$run/out/$k.$m.out"; then
      if cmp -s "$o.sel" <(rows "$run/out/$k.$m.out" | sed -n 's/^\([^ ]*\) \([^ ]*\)$/\1.\2/p' | sort -u)
      then line+=" $m=exact"; else line+=" $m=diff"; fi
    else line+=" $m=-"; fi
  done
  echo "$line"
}

# <slot> <key>: whether 0install takes mccs's answer for the query
accept() {
  local slot=$1 k=$2 o=$M/out/$2 rc a=error
  OPAMROOT=$M/root.$slot timeout "$TIMEOUT" opam install $(cat "$o.sel") --dry-run \
    --solver=builtin-0install --switch cmp --no-depexts -y > "$o.accept" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then
    if cmp -s "$o.sel" <(sed -n 's/^.*installed \([^ ]*\)$/\1/p' "$o.accept" | sort -u); then a=yes; else a=no; fi
  elif refused "$rc" "$o.accept"; then a=no; fi
  echo "query=$k accepted=$a"
}

# each worker its own OPAMROOT and its share of the keys, one per line
work() {  # <slot> <fn> <keys-file>
  local slot=$1 fn=$2 k
  rm -rf "$M/root.$slot"; cp -r "$run/opamroot" "$M/root.$slot"
  while IFS= read -r k; do
    if [ "$fn" = one ]; then one "$slot" "$k" $(python3 "$S/../triage_lib.py" unkey "$k")
    else accept "$slot" "$k"; fi
  done < "$3" > "$M/part.$slot"
  rm -rf "$M/root.$slot"
}

fanout() {  # <fn> <keys-file> <out>
  local i
  rm -f "$M"/keys.* "$M"/part.*
  split -n "r/$P" -d -a 3 "$2" "$M/keys."
  for i in "$M"/keys.*; do work "${i##*.}" "$1" "$i" & done
  wait
  cat "$M"/part.* | sort > "$3"
  rm -f "$M"/keys.* "$M"/part.*
}

if [ -z "$acc" ]; then
  cut -f1 "$run/keys" > "$M/todo"
  fanout one "$M/todo" "$run/mccs.txt"
  awk '{for (i = 2; i <= NF; i++) n[$i]++} END {for (x in n) print n[x], x}' "$run/mccs.txt" | sort -k2
else
  [ -s "$run/mccs.txt" ] || { echo "$0: no mccs.txt in $run; run without --accept first" >&2; exit 1; }
  awk '/ tool=diff/ {sub(/^query=/, "", $1); print $1}' "$run/mccs.txt" |
    python3 -c 'import random, sys; ks = sys.stdin.read().split(); r = random.Random(int(sys.argv[2]))
print("\n".join(sorted(r.sample(ks, min(int(sys.argv[1]), len(ks))))))' "$acc" "$seed" > "$M/accept.todo"
  fanout accept "$M/accept.todo" "$run/mccs-accept.txt"
  awk '{n[$2]++} END {for (x in n) print n[x], x}' "$run/mccs-accept.txt" | sort -k2
fi
