# Sourced by each eval/<eco>/scale.sh, which defines one -- a goal's result
# lines, one per mode, from its key and goal -- all_goals and prepare, and
# then calls main.
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

compare() {  # <ours> <theirs>, both sorted
  oo=$(comm -23 "$1" "$2" | wc -l); to=$(comm -13 "$1" "$2" | wc -l)
  if [ $((oo + to)) -eq 0 ]; then corr=exact; else corr=diff; fi
}

# valid.sh writes under its own out/<tag>; a tag relative to that puts its
# files in the run directory instead
valid() {  # <recorded answer> <mode> <goal>
  local tag
  tag=$(realpath -m --relative-to="$S/out" "$run/valid/$2")
  valid=$(REPLAY=$1 EXTRA=$(flag "$2") timeout "$TIMEOUT" \
    bash "$S/valid.sh" "$S/scale.sh" "$tag" "$3" 2>/dev/null |
    awk '$NF == "VALID" || $NF == "INVALID" {v = $NF} END {print (v ? v : "ERR")}')
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
  [ $# -ge 2 ] || { echo "usage: $0 <pac-exe> <run-dir> [goals-file]" >&2; exit 2; }
  if [ "$1" = --one ]; then
    local k=${2%%$'\t'*}
    one "$k" "${2#*$'\t'}" > "$run/res/.$k" && mv "$run/res/.$k" "$run/res/$k"
    exit
  fi
  mkdir -p "$2/res" "$2/out" || exit 1
  run=$(cd "$2" && pwd); export run
  # one binary per run, so a resumed run never mixes two
  if [ -e "$run/pac.exe" ]; then
    cmp -s "$1" "$run/pac.exe" || { echo "$0: $run was started with another pac" >&2; exit 1; }
  else cp "$1" "$run/pac.exe"; fi
  prepare || exit 1
  if [ -n "${3:-}" ]; then cp "$3" "$run/goals.txt" || exit 1
  elif [ ! -s "$run/goals.txt" ]; then all_goals > "$run/goals.txt"; fi
  ls "$run/res" | awk -F'\t' 'FILENAME == "-" {done[$0]; next}
    NF {k = $NF; gsub(/%/, "%25", k); gsub(/\+/, "%2B", k); gsub(/\//, "%2F", k); gsub(/ /, "+", k)
        if (!(k in done)) {done[k]; print k "\t" $NF}}' - "$run/goals.txt" > "$run/todo"
  echo "$0: $(wc -l < "$run/todo") of $(wc -l < "$run/goals.txt") goals to run" >&2
  xargs -r -P "$P" -d '\n' -n 1 bash "$0" --one < "$run/todo"
  find "$run/res" -type f ! -name '.*' -exec cat {} + | sort > "$run/results.txt"
}
