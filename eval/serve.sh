# Sourced wherever shim.py or sparse_proxy.py is started.  Each answers
# /-/pac-serves with the directory it serves, so that a server some other
# run left on the port, which the new one cannot bind, is never taken for
# this run's: a server that is merely alive may be the other one.
serve() {  # <port> <dir served> <log> <command...>: the server's pid in served
  local port=$1 want have= i log=$3
  want=$(realpath "$2"); shift 3
  "$@" > "$log" 2>&1 &
  served=$!
  trap "kill $served 2> /dev/null" EXIT
  for i in $(seq 50); do
    have=$(curl -sf "http://127.0.0.1:$port/-/pac-serves") && break
    sleep 0.2
  done
  kill -0 "$served" 2> /dev/null && [ "$have" = "$want" ] ||
    { echo "$0: the server on $port is not this run's (serving '${have:-nothing}')" >&2; return 1; }
}
