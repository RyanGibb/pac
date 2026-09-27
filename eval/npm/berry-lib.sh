# Sourced by berryall.sh and berryownall.sh.

# a scale.sh run of READING=shared, whose answers alone Berry must take,
# and one berryreg.py over its snapshot farm, on the port given
berry_run() {  # <run-dir> <port> <log>
  run=$(cd "$1" && pwd) port=$2
  grep -qx 'READING=shared' "$run/params" ||
    { echo "$0: $run was not run with READING=shared" >&2; exit 2; }
  . "$S/../serve.sh"
  serve "$port" "$run/cache" "$run/$3" python3 "$S/berryreg.py" "$port" "$run/cache" || exit 1
  export NPM_RUN=$run BPORT=$port S
}
