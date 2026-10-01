#!/usr/bin/env bash
# usage: check.sh <eco> <answer> <out-dir> <query...>
# The query is what pac was asked, in the words pac took; the answer is
# pac's output.  The last line printed ends in the verdicts valid=, minimal=
# and reproduced=, as eval/README.md's Validity check defines them.
set -u
E="$(cd "$(dirname "$0")" && pwd)"
[ $# -ge 3 ] && [ -f "$E/$1/check.sh" -o -f "$E/$1/check.py" ] ||
  { echo "usage: $0 <eco> <answer> <out-dir> <query...>" >&2; exit 2; }
eco=$1 ans=$(realpath "$2") out=$(realpath -m "$3"); shift 3
mkdir -p "$out" || exit 1
. "$E/answer.sh"
export -f rows whole
if [ -f "$E/$eco/check.py" ]; then exec python3 "$E/$eco/check.py" "$ans" "$out" "$@"; fi
exec bash "$E/$eco/check.sh" "$ans" "$out" "$@"
