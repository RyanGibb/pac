#!/usr/bin/env bash
# usage: check-misses.sh <miss-log>
# A refused name npm needed means the lock was not computed from the
# snapshot, so the run is not a measurement; say which, and fail.
S="$(cd "$(dirname "$0")" && pwd)"
bad=$(sort -u "$1" | grep -vxF -f <(sed -e 's/#.*//' -e 's/[[:space:]]*$//' \
                                       -e '/^$/d' "$S/tolerated-misses"))
[ -z "$bad" ] && exit 0
echo "FAIL: the frozen shim refused names the snapshot does not hold:"
printf '  %s\n' $bad
exit 1
