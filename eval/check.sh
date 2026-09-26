#!/usr/bin/env bash
# usage: check.sh <eco> <answer> <out-dir> <query...>
# The query is what pac was asked, in the words pac took; the answer is
# pac's output.  The last line printed ends in two verdicts:
#   valid=VALID|INVALID|CYCLIC|ERR  whether the tool takes the answer as
#     consistent: every package's dependencies met, no conflict, one version
#     of a name where the tool allows one.  CYCLIC is a resolution the tool
#     cannot install for a cycle in its install order; ERR, that the check
#     could not be run to a verdict.
#   minimal=yes|no|-  whether the tool, left to settle the answer for the
#     query alone, would keep it as it stands rather than remove or swap
#     something; - where the answer is not VALID.
# The core calculus asks a resolution for no minimality, so only valid
# counts against pac.
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
