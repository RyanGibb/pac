#!/usr/bin/env bash
# Whether Yarn Berry takes our answer under the shared reading: the answer
# is written out as a Berry project (berrylock.py) against berryreg.py on
# BPORT; `yarn install --immutable --check-resolutions` must accept the
# lock, `yarn explain peer-requirements` mark no requirement unmet (YN0002,
# YN0060), and under PnP every row must load the copy it names
# (berryprobe.cjs).  A peer the answer leaves open that PnP's fallback
# fills, and a package Berry disabled for another os or cpu, are counted
# apart.
# usage: berry.sh <answer> <out-dir> <query...>
#        NPM_RUN=<run with cache/> BPORT=<berryreg.py port>
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
. "$S/berry-lib.sh"
yarn_check
RUN=${NPM_RUN:?} BPORT=${BPORT:?}
ans=$1 out=$2; shift 2
W=$out/berry
verdict() {  # <valid> <why>
  printf '%s berry=%s\n' "$2" "$1"
  exit 0
}
case "$W" in */berry) rm -rf "$W" ;; esac
mkdir -p "$W/.home"
export HOME=$W/.home XDG_CACHE_HOME=$W/.home/.cache YARN_ENABLE_TELEMETRY=0 \
  CI=1 NO_COLOR=1 FORCE_COLOR=0
python3 "$S/berrylock.py" prepare "$RUN/cache" "$ans" "$W" "$BPORT" "$@" > "$out/berry.prepare" 2>&1 ||
  verdict ERR "prepare failed: $(tail -n 1 "$out/berry.prepare" | cut -c 1-200)"
(cd "$W" && timeout 1800 yarn install) > "$out/berry.i1" 2>&1
i1=$?
[ $i1 -eq 0 ] || verdict ERR "i1=$i1 $(grep -o 'YN0[0-9]*: .*' "$out/berry.i1" | grep -v YN0000 | head -n 1 | cut -c 1-200)"
python3 "$S/berrylock.py" patch "$W" > "$out/berry.patch" 2>&1 || verdict ERR "patch failed"
(cd "$W" && timeout 1800 yarn install) > "$out/berry.i2" 2>&1
i2=$?
python3 "$S/berrylock.py" compare "$W" > "$out/berry.compare" 2>&1
off=$(sed -n 's/^descriptors [0-9]*, off \([0-9]*\)$/\1/p' "$out/berry.compare")
(cd "$W" && timeout 1800 yarn install --immutable --check-resolutions) > "$out/berry.i3" 2>&1
i3=$?
(cd "$W" && timeout 600 yarn explain peer-requirements) > "$out/berry.explain" 2>&1
ex=$?
cross=$(grep -c '✘' "$out/berry.explain")
pnp=ERR
if [ -f "$W/.pnp.cjs" ]; then
  (cd "$W" && timeout 600 node -r ./.pnp.cjs "$S/berryprobe.cjs" expect.json) > "$out/berry.probe" 2> "$out/berry.probe.err"
  pnp=$(python3 -c 'import json,sys
c=json.load(open(sys.argv[1]))["counts"]
print(sum(c[k] for k in ("wrong", "unloaded", "peerWrong", "peerMissing")), c["disabled"], c["fallback"])' "$out/berry.probe" 2>/dev/null || echo ERR)
fi
read -r split extra < <(python3 -c 'import json,sys
p=json.load(open(sys.argv[1])); print(len(p["split"]), len(p["extra"]))' "$W/pins.json")
why="i1=$i1 i2=$i2 off=${off:--} i3=$i3 explain=$ex unmet=$cross split=$split extra=$extra"
why="$why pnp-miss/disabled/fallback=${pnp// //}"
[ "$pnp" != ERR ] && [ $i2 -eq 0 ] && [ $ex -eq 0 ] && [ -n "$off" ] || verdict ERR "$why"
[ $i3 -eq 0 ] && [ "$off" -eq 0 ] && [ "$cross" -eq 0 ] && [ "$split" -eq 0 ] &&
  [ "$extra" -eq 0 ] && [ "${pnp%% *}" -eq 0 ] || verdict INVALID "$why"
verdict VALID "$why"
