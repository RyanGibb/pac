#!/usr/bin/env bash
# usage: controls.sh <scratch-dir>        PORT=<free port for the proxy>
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
T=$(mkdir -p "$1" && cd "$1" && pwd)
export PORT=${PORT:-8991} CARGO_INDEX=$T/index
bad=0

# a fixture index: alpha 1.0.0, 1.1.0 and 2.0.0; zeta 1.0.0 needing beta,
# and zeta 2.0.0 needing nothing
rm -rf "$T/index"
python3 - "$T/index" <<'EOF'
import hashlib, json, os, sys
T = sys.argv[1]
ROWS = {"alpha": [("1.0.0", []), ("1.1.0", []), ("2.0.0", [])],
        "beta": [("1.0.0", [])],
        "zeta": [("1.0.0", [{"name": "beta", "req": "^1"}]), ("2.0.0", [])]}
for n, vs in ROWS.items():
    d = os.path.join(T, n[:2], n[2:4])
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, n), "w") as f:
        for v, deps in vs:
            f.write(json.dumps({"name": n, "vers": v, "features": {}, "yanked": False,
                                "cksum": hashlib.sha256(f"{n}{v}".encode()).hexdigest(),
                                "deps": [dict(features=[], optional=False, default_features=True,
                                              target=None, kind="normal", **x) for x in deps]}) + "\n")
EOF
mkdir -p "$T/root/src"
: > "$T/root/src/lib.rs"
printf '[package]\nname = "root"\nversion = "1.0.0"\nedition = "2015"\n\n[lib]\npath = "src/lib.rs"\n\n[dependencies]\nalpha = "^1"\n' \
  > "$T/root/Cargo.toml"

. "$S/../serve.sh"
serve "$PORT" "$T/index" "$T/proxy.log" python3 "$S/sparse_proxy.py" "$PORT" "$T/index" || exit 1

# the answer as pac prints it: crates, then "parent child version" edges;
# the expected verdicts as valid/minimal
ctl() {  # <name> <expected> <crates> <edges>
  local name=$1 want=$2 d=$T/$1 got e c=($3) es=($4)
  rm -rf "$d"; mkdir -p "$d"
  { echo "root root 1.0.0"; echo "packages (${#c[@]}):"; printf '  %s\n' "${c[@]}" | tr _ ' '
    echo "parent edges (${#es[@]}):"
    for e in "${es[@]}"; do
      set -- ${e//_/ }
      echo "  $1 $2 -> $3($3) $4"
    done; } > "$d/ans.out"
  got=$(bash "$S/../check.sh" cargo "$d/ans.out" "$d/check" "$T/root/Cargo.toml" |
    tail -n 1 | sed -n 's/.* valid=\([A-Z]*\) minimal=\(.*\)$/\1\/\2/p')
  printf '%-12s expect %-11s got %s\n' "$name" "$want" "$got"
  [ "$got" = "$want" ] || bad=1
}

ctl ok VALID/yes 'root_1.0.0 alpha_1.1.0' 'root_1.0.0_alpha_1.1.0'
# older than cargo would pick, and still admitted: cargo keeps it
ctl old VALID/yes 'root_1.0.0 alpha_1.0.0' 'root_1.0.0_alpha_1.0.0'
ctl missing INVALID/- 'root_1.0.0' ''
ctl range INVALID/- 'root_1.0.0 alpha_2.0.0' 'root_1.0.0_alpha_2.0.0'
# nothing reaches zeta: cargo drops it
ctl extra VALID/no 'root_1.0.0 alpha_1.1.0 zeta_2.0.0' 'root_1.0.0_alpha_1.1.0'
# and does not ask what zeta 1.0.0 needs, which the answer lacks
ctl extra-broken INVALID/- 'root_1.0.0 alpha_1.1.0 zeta_1.0.0' 'root_1.0.0_alpha_1.1.0'

# cargo failing for want of a registry says nothing of the answer
kill $served; wait $served 2> /dev/null
ctl noproxy ERR/- 'root_1.0.0 alpha_1.1.0' 'root_1.0.0_alpha_1.1.0'

exit $bad
