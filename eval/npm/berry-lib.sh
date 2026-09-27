# Sourced by berry.sh, berryall.sh and berryownall.sh.  The Yarn Berry
# whose packageExtensions lib/npm/berry-extensions.json lists, as
# nix/flake.lock pins it.
YARN_VERSION=4.14.1

yarn_check() {
  local v
  v=$(cd / && yarn --version 2> /dev/null)
  [ "$v" = "$YARN_VERSION" ] ||
    { echo "$0: yarn ${v:-missing}, not $YARN_VERSION" >&2; exit 2; }
}

# a scale.sh run of READING=shared, whose answers alone Berry must take,
# and one berryreg.py over its snapshot farm, on the port given
berry_run() {  # <run-dir> <port> <log>
  run=$(cd "$1" && pwd) port=$2
  grep -qx 'READING=shared' "$run/params" ||
    { echo "$0: $run was not run with READING=shared" >&2; exit 2; }
  yarn_check
  . "$S/../serve.sh"
  serve "$port" "$run/cache" "$run/$3" python3 "$S/berryreg.py" "$port" "$run/cache" || exit 1
  export NPM_RUN=$run BPORT=$port S
}
