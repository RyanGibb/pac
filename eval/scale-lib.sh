# Sourced by each eval/<eco>/scale.sh, which defines one -- a query's result
# lines, one per mode, from its key and the query, a whole one in the tool's
# own syntax, flags included -- all_queries and prepare, may redefine
# regress_queries and define totals, and then calls main.
set -u
export LC_ALL=C
E="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOP="$(dirname "$E")"
export P="${P:-$(nproc)}" TIMEOUT="${TIMEOUT:-900}" MODES="${MODES:-default}"

# valid.sh runs the <exe> it is handed; handed scale.sh with REPLAY set, it
# is given the answer the run already compared rather than a second solve
if [ -n "${REPLAY:-}" ]; then cat "$REPLAY.out"; exit "$(cat "$REPLAY.rc")"; fi

flag() { [ "$1" = default ] || printf -- '--%s' "$1"; }

since() { awk -v a="$1" -v b="$EPOCHREALTIME" 'BEGIN {printf "%.2f", b - a}'; }

pac_status() {  # <rc> <output> <line the answer starts with>
  # cmdliner exits 124 too, on a usage error
  if [ "$1" -eq 124 ] && ! grep -q '^Usage: ' "$2"; then echo timeout
  elif [ "$1" -eq 0 ] && grep -q "$3" "$2"; then echo ok
  elif grep -q '^unsatisfiable' "$2"; then echo unsat
  else echo crash; fi
}

tool_status() {  # <rc> <answer>
  if [ "$1" -eq 124 ]; then echo timeout
  elif [ "$1" -eq 0 ] && [ -s "$2" ]; then echo ok
  else echo refuse; fi
}

regress_queries() { cat "$S/queries.txt"; }

# The tool's answer into $o.theirs, its status into tool and its wall time
# into twall: asked afresh, or under --regress read back from the
# baseline, <stem>.<ext> for an answer and <stem>.absent for a refusal,
# which --record writes
answer() {  # <baseline stem> <ext> <command asking the tool into $o.theirs>
  local b=$1.$2 a=$1.absent t0=$EPOCHREALTIME rc; shift 2
  twall=-
  if [ "$BASELINE" = regress ]; then
    : > "$o.theirs"
    if [ -e "$a" ]; then tool=refuse
    elif [ -s "$b" ]; then cp "$b" "$o.theirs"; tool=ok
    else tool=unrecorded; fi
    return
  fi
  "$@"; rc=$?
  twall=$(since "$t0")
  tool=$(tool_status $rc "$o.theirs")
  if [ "$BASELINE" = record ]; then
    rm -f "$b" "$a"
    case $tool in ok) cp "$o.theirs" "$b" ;; refuse) : > "$a" ;; esac
  fi
}

compare() {  # <ours> <theirs>, both sorted
  oo=$(comm -23 "$1" "$2" | wc -l); to=$(comm -13 "$1" "$2" | wc -l)
  if [ $((oo + to)) -eq 0 ]; then corr=exact; else corr=diff; fi
}

# valid.sh writes under its own out/<tag>; a tag relative to that puts its
# files in the run directory instead
valid() {  # <recorded answer> <mode> <query>
  local tag
  tag=$(realpath -m --relative-to="$S/out" "$run/valid/$2")
  valid=$(REPLAY=$1 EXTRA=$(flag "$2") timeout "$TIMEOUT" \
    bash "$S/valid.sh" "$S/scale.sh" "$tag" "$3" 2>/dev/null |
    awk '$NF ~ /^(VALID|INVALID|CYCLIC)$/ {v = $NF} END {print (v ? v : "ERR")}')
}

snapshot() {  # <path under repos/>
  local p=$TOP/repos/$1 id
  if [ -d "$p/.git" ]; then
    id=$(git -C "$p" rev-parse HEAD)
    [ -z "$(git -C "$p" status --porcelain)" ] || id=$id-dirty
  elif [ -d "$p" ]; then
    id=$(cd "$p" && find . -type f -printf '%P\n' | sort | tr '\n' '\0' |
         xargs -0 sha256sum | awk '{print $1}' | sort | sha256sum | cut -d' ' -f1)
  else
    id=$(sha256sum < "$p" | cut -d' ' -f1)
  fi
  awk -v p="repos/$1" -v id="$id" '$1 == p && $2 == id {ok = 1} END {exit !ok}' \
    "$E/SNAPSHOTS" || { echo "$0: repos/$1 is $id, not what eval/SNAPSHOTS records" >&2; exit 1; }
}

main() {
  if [ "${1:-}" = --one ]; then
    local k=${2%%$'\t'*}
    one "$k" "${2#*$'\t'}" > "$run/res/.$k" && mv "$run/res/.$k" "$run/res/$k"
    exit
  fi
  case ${1:-} in --regress|--record) BASELINE=${1#--}; shift ;; *) BASELINE= ;; esac
  export BASELINE
  [ $# -ge 2 ] || { echo "usage: $0 [--regress | --record] <pac-exe> <run-dir> [queries-file]" >&2; exit 2; }
  mkdir -p "$2/res" "$2/out" || exit 1
  run=$(cd "$2" && pwd); export run
  # one binary and one source of answers per run, so a resumed run never mixes two
  if [ -e "$run/pac.exe" ]; then
    cmp -s "$1" "$run/pac.exe" || { echo "$0: $run was started with another pac" >&2; exit 1; }
    [ "$(cat "$run/baseline" 2> /dev/null)" = "$BASELINE" ] || { echo "$0: $run was started in another mode" >&2; exit 1; }
  else cp "$1" "$run/pac.exe"; echo "$BASELINE" > "$run/baseline"; fi
  prepare || exit 1
  if [ -n "${3:-}" ]; then cp "$3" "$run/queries.txt" || exit 1
  elif [ ! -s "$run/queries.txt" ]; then
    if [ -n "$BASELINE" ]; then regress_queries; else all_queries; fi > "$run/queries.txt"
  fi
  ls "$run/res" | awk -F'\t' 'FILENAME == "-" {done[$0]; next}
    NF {k = $NF; gsub(/%/, "%25", k); gsub(/\+/, "%2B", k); gsub(/\//, "%2F", k); gsub(/ /, "+", k)
        if (!(k in done)) {done[k]; print k "\t" $NF}}' - "$run/queries.txt" > "$run/todo"
  echo "$0: $(wc -l < "$run/todo") of $(wc -l < "$run/queries.txt") queries to run" >&2
  xargs -r -P "$P" -d '\n' -n 1 bash "$0" --one < "$run/todo"
  find "$run/res" -type f ! -name '.*' -exec cat {} + | sort > "$run/results.txt"
  awk -v modes="$MODES" '
    {for (i = 1; i <= NF; i++) {j = index($i, "="); f[substr($i, 1, j - 1)] = substr($i, j + 1)}
     m = f["mode"]; n[m]++; un[m] += f["tool"] == "unrecorded"
     if (f["tool"] == "ok") {ans[m]++; ex[m] += f["corr"] == "exact"}
     if (f["valid"] != "-") {chk[m]++; ok[m] += f["valid"] == "VALID"}}
    END {k = split(modes, ms, " ")
      for (i = 1; i <= k; i++) if (ms[i] in n)
        printf "%s: %d queries, exact %d/%d, valid %d/%d%s\n", ms[i], n[ms[i]], ex[ms[i]], ans[ms[i]],
          ok[ms[i]], chk[ms[i]], un[ms[i]] ? ", unrecorded " un[ms[i]] : ""}' "$run/results.txt"
  if declare -F totals > /dev/null; then totals; fi
}
