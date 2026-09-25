# Sourced by each eval/<eco>/scale.sh, which sets ECO and ANSWER (the line
# pac's answer starts with) and defines all_queries, prepare, ask_tool <key>
# <query> (the tool's answer into $o.theirs and its status into tool, as a
# rule through answer), run_pac <mode> <stem> <query> (pac's output into
# <stem>.out) and extract <stem> (<stem>.ours, sorted, what correspond
# compares), and then calls main.  It may also define refused, pin_tool,
# correspond, canon, check_query, fields, emit, params, regress_queries and
# totals, each described where the default is.
set -u
export LC_ALL=C
E="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOP="$(dirname "$E")"
export P="${P:-$(nproc)}" TIMEOUT="${TIMEOUT:-900}" MODES="${MODES:-tool pubgrub}"

flag() { printf -- '--order=%s' "$1"; }

since() { awk -v a="$1" -v b="$EPOCHREALTIME" 'BEGIN {printf "%.2f", b - a}'; }

pac_status() {  # <rc> <output> <line the answer starts with>
  # cmdliner exits 124 too, on a usage error
  if [ "$1" -eq 124 ] && ! grep -q '^Usage: ' "$2"; then echo timeout
  elif [ "$1" -eq 0 ] && grep -q "$3" "$2"; then echo ok
  elif grep -q '^unsatisfiable' "$2"; then echo unsat
  else echo crash; fi
}

# whether a failed tool run is the tool saying the query has no answer; any
# other failure is the tool's error, a class of its own that --record never
# writes down as a refusal
refused() { return 1; }  # <rc> <log>

tool_status() {  # <rc> <answer> <log>
  if [ "$1" -eq 124 ]; then echo timeout
  elif [ "$1" -eq 0 ] && [ -s "$2" ]; then echo ok
  elif [ "$1" -ne 0 ] && refused "$1" "$3"; then echo refuse
  else echo error; fi
}

regress_queries() { cat "$S/queries.txt"; }

# The tool's answer into $o.theirs, its status into tool and its wall time
# into twall: asked afresh, or under --regress read back from the
# baseline, <stem>.<ext> for an answer and <stem>.absent for a refusal,
# which --record writes
answer() {  # <baseline stem> <ext> <tool log> <command asking the tool into $o.theirs>
  local b=$1.$2 a=$1.absent log=$3 t0=$EPOCHREALTIME rc; shift 3
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
  tool=$(tool_status $rc "$o.theirs" "$log")
  if [ "$BASELINE" = record ]; then
    case $tool in
      ok) rm -f "$a"; cp "$o.theirs" "$b" ;;
      refuse) rm -f "$b"; : > "$a" ;;
      *) echo "$0: $1: the tool gave no answer ($tool), so nothing is recorded" >&2 ;;
    esac
  fi
}

compare() {  # <ours> <theirs>, both sorted
  oo=$(comm -23 "$1" "$2" | wc -l); to=$(comm -13 "$1" "$2" | wc -l)
  if [ $((oo + to)) -eq 0 ]; then corr=exact; else corr=diff; fi
}

correspond() { compare "$1.ours" "$o.theirs"; }  # <stem>

# what the check reads of an answer, so that a mode answering the same gets
# the same verdict; failing, every mode is checked
canon() { cat "$1.ours"; }  # <stem>

check_query() { printf '%s\n' "$2"; }  # <stem> <query>

# eval/check.sh's two verdicts on <stem>.out, its files under <stem>.check;
# no verdict at all, a timeout among them, is ERR
check() {  # <stem> <query words...>
  local p=$1 v; shift
  mkdir -p "$p.check"
  timeout "$TIMEOUT" bash "$E/check.sh" "$ECO" "$p.out" "$p.check" "$@" > "$p.check/log" 2>&1
  v=" $(tail -n 1 "$p.check/log")"
  valid=$(sed -n 's/.* valid=\([A-Z]*\)\( .*\)\{0,1\}$/\1/p' <<< "$v")
  minimal=$(sed -n 's/.* minimal=\([a-z-]*\)\( .*\)\{0,1\}$/\1/p' <<< "$v")
  case $valid in VALID|INVALID|CYCLIC) ;; *) valid=ERR ;; esac
  [ "$valid" = VALID ] && [ -n "$minimal" ] || minimal=-
}

fields() { :; }  # <stem>: extra fields of a mode's line, each " k=v"

emit() { printf '%s' "$1"; }  # <the query's lines>

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

one() {  # <key> <query>
  local o=$run/out/$1 m p pac tool twall corr valid minimal oo to t0 wall pin=- last= lastv lastm a b lines=
  set -f
  ask_tool "$1" "$2"
  # pin_tool asks pac for the tool's own answer, into pin: ok, unsat, or no
  # verdict; only an unsat makes a divergence an instance gap
  if [ "$tool" = ok ] && declare -F pin_tool > /dev/null; then pin_tool "$1" "$2"; fi
  for m in $MODES; do
    p=$o.$m corr=- valid=- minimal=- oo=- to=- t0=$EPOCHREALTIME
    rm -rf "$p.check"
    run_pac "$m" "$p" "$2"
    echo $? > "$p.rc"
    wall=$(since "$t0")
    pac=$(pac_status "$(cat "$p.rc")" "$p.out" "$ANSWER")
    extract "$p"
    [ "$pac" = ok ] && [ "$tool" = ok ] && correspond "$p"
    if [ "$pac" = ok ]; then
      if [ -n "$last" ] && a=$(canon "$p") && b=$(canon "$last") && [ "$a" = "$b" ]; then
        valid=$lastv minimal=$lastm
        ln -sfn -- "${last##*/}.check" "$p.check"
      else
        check "$p" $(check_query "$p" "$2")
      fi
      last=$p lastv=$valid lastm=$minimal
    fi
    lines+="query=$1 mode=$m pac=$pac tool=$tool corr=$corr valid=$valid minimal=$minimal oo=$oo to=$to wall=$wall pin=$pin$(fields "$p")"$'\n'
  done
  emit "$lines"
}

params() { :; }  # what else a resumed run must share with the run it resumes

main() {
  if [ "${1:-}" = --one ]; then
    local k=${2%%$'\t'*}
    one "$k" "${2#*$'\t'}" > "$run/res/.$k" && mv "$run/res/.$k" "$run/res/$k"
    exit
  fi
  case ${1:-} in --regress|--record) BASELINE=${1#--}; shift ;; *) BASELINE= ;; esac
  export BASELINE
  [ $# -ge 2 ] || { echo "usage: $0 [--regress | --record] <pac-exe> <run-dir> [queries-file]" >&2; exit 2; }
  local m
  for m in $MODES; do
    case $m in tool|pubgrub) ;; *) echo "$0: mode $m is neither tool nor pubgrub" >&2; exit 2 ;; esac
  done
  mkdir -p "$2/res" "$2/out" || exit 1
  run=$(cd "$2" && pwd); export run
  local q=$run/queries.txt
  if [ -n "${3:-}" ]; then q=$(realpath "$3") || exit 1
  elif [ ! -s "$q" ]; then
    if [ -n "$BASELINE" ]; then regress_queries; else all_queries; fi > "$run/queries.new" &&
      mv "$run/queries.new" "$q" || exit 1
  fi
  # one binary, one source of answers and one set of parameters per run, so a
  # resumed run never mixes two
  { echo "baseline=$BASELINE"; echo "MODES=$MODES"; echo "TIMEOUT=$TIMEOUT"; params
    echo "queries=$(sha256sum < "$q" | cut -d' ' -f1)"; } > "$run/params.new"
  if [ -e "$run/pac.exe" ]; then
    cmp -s "$1" "$run/pac.exe" || { echo "$0: $run was started with another pac" >&2; exit 1; }
    cmp -s "$run/params.new" "$run/params" ||
      { echo "$0: $run was started with other parameters:" >&2
        diff "$run/params" "$run/params.new" >&2; exit 1; }
  else cp "$1" "$run/pac.exe"; mv "$run/params.new" "$run/params"; fi
  rm -f "$run/params.new"
  [ "$q" = "$run/queries.txt" ] || cp "$q" "$run/queries.txt" || exit 1
  prepare || exit 1
  python3 "$E/triage_lib.py" keys < "$run/queries.txt" > "$run/keys" || exit 1
  ls "$run/res" | awk -F'\t' 'FILENAME == "-" {done[$1]; next} !($1 in done)' - "$run/keys" > "$run/todo"
  echo "$0: $(wc -l < "$run/todo") of $(wc -l < "$run/keys") queries to run" >&2
  xargs -r -P "$P" -d '\n' -n 1 bash "$0" --one < "$run/todo"
  # only the queries of this queries.txt, and each one that has no result
  # named, since a failed worker leaves none
  local missing
  missing=$(comm -23 <(cut -f1 "$run/keys" | sort) <(ls "$run/res" | sort))
  comm -12 <(cut -f1 "$run/keys" | sort) <(ls "$run/res" | sort) |
    (cd "$run/res" && xargs -r -d '\n' cat --) | sort > "$run/results.txt"
  awk -v modes="$MODES" '
    {delete f; for (i = 1; i <= NF; i++) {j = index($i, "="); f[substr($i, 1, j - 1)] = substr($i, j + 1)}
     m = f["mode"]; n[m]++; un[m] += f["tool"] == "unrecorded"; te[m] += f["tool"] == "error"
     if (f["tool"] == "ok") {ans[m]++; ex[m] += f["corr"] == "exact"}
     if (f["valid"] ~ /^(VALID|INVALID)$/) {chk[m]++; ok[m] += f["valid"] == "VALID"}
     if (f["valid"] == "VALID") mi[m] += f["minimal"] == "yes"
     cy[m] += f["valid"] == "CYCLIC"; er[m] += f["valid"] == "ERR"}
    END {k = split(modes, ms, " ")
      for (i = 1; i <= k; i++) if (ms[i] in n) {
        m = ms[i]
        printf "%s: %d queries, exact %d/%d, valid %d/%d, minimal %d/%d", m, n[m], ex[m], ans[m], ok[m], chk[m], mi[m], ok[m]
        if (cy[m]) printf ", cyclic %d", cy[m]
        if (er[m]) printf ", unchecked %d", er[m]
        if (te[m]) printf ", tool error %d", te[m]
        if (un[m]) printf ", unrecorded %d", un[m]
        print ""}}' "$run/results.txt"
  if declare -F totals > /dev/null; then totals; fi
  if [ -n "$missing" ]; then
    echo "missing $(wc -l <<< "$missing") of $(wc -l < "$run/keys") queries, whose worker failed:" $missing
    exit 1
  fi
}
