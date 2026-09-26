#!/usr/bin/env bash
# usage: controls.sh <scratch-dir>        PORT=<free port for the proxy>
set -u
export LC_ALL=C
S="$(cd "$(dirname "$0")" && pwd)"
T=$(mkdir -p "$1" && cd "$1" && pwd)
export PORT=${PORT:-8991} CARGO_INDEX=$T/index
bad=0

# a fixture index: alpha 1.0.0, 1.1.0 and 2.0.0; zeta 1.0.0 needing beta,
# and zeta 2.0.0 needing nothing; split declaring wsys twice, under two cfgs,
# and hold needing wsys 2; opt's beta optional behind feature fb, and devy's
# a dev-dependency; kz declaring zed twice, with ranges that overlap; lsys
# and lsysb both linking lx
rm -rf "$T/index"
python3 - "$T/index" <<'EOF'
import hashlib, json, os, sys
T = sys.argv[1]
ROWS = {"alpha": [("1.0.0", []), ("1.1.0", []), ("2.0.0", [])],
        "beta": [("1.0.0", [])],
        "zeta": [("1.0.0", [{"name": "beta", "req": "^1"}]), ("2.0.0", [])],
        "wsys": [("1.0.0", []), ("2.0.0", [])],
        "split": [("1.0.0", [{"name": "wsys", "req": ">=1, <3", "target": "cfg(windows)"},
                             {"name": "wsys", "req": ">=1, <3", "target": "cfg(unix)"}])],
        "hold": [("1.0.0", [{"name": "wsys", "req": "^2"}])],
        "opt": [("1.0.0", [{"name": "beta", "req": "^1", "optional": True}], {"fb": ["beta"]})],
        "devy": [("1.0.0", [{"name": "beta", "req": "^1", "kind": "dev"}])],
        "zed": [("1.0.0", []), ("1.9.0", []), ("2.5.0", [])],
        "kz": [("1.0.0", [{"name": "zed", "req": "^1"},
                          {"name": "zed", "req": ">=1, <3", "kind": "build"}])],
        "lsys": [("1.0.0", [], {}, "lx")],
        "lsysb": [("1.0.0", [], {}, "lx")]}
for n, vs in ROWS.items():
    d = (os.path.join(T, n[:2], n[2:4]) if len(n) > 3 else
         os.path.join(T, "3", n[0]) if len(n) == 3 else os.path.join(T, str(len(n))))
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, n), "w") as f:
        for v, deps, *more in vs:
            row = {"name": n, "vers": v, "features": more[0] if more else {}, "yanked": False,
                   "cksum": hashlib.sha256(f"{n}{v}".encode()).hexdigest(),
                   "deps": [{"features": [], "optional": False, "default_features": True,
                             "target": None, "kind": "normal", **x} for x in deps]}
            if len(more) > 1:
                row["links"] = more[1]
            f.write(json.dumps(row) + "\n")
EOF
root() {  # <dir> <dependency lines...>
  mkdir -p "$T/$1/src"
  : > "$T/$1/src/lib.rs"
  { printf '[package]\nname = "root"\nversion = "1.0.0"\nedition = "2015"\n\n[lib]\npath = "src/lib.rs"\n\n[dependencies]\n'
    shift; printf '%s\n' "$@"; } > "$T/$1/Cargo.toml"
}
root root 'alpha = "^1"'
root root-split 'split = "=1.0.0"'
root root-held 'split = "=1.0.0"' 'hold = "^1"'
root root-opt 'opt = "=1.0.0"'
root root-devy 'devy = "=1.0.0"'
root root-kz 'kz = "=1.0.0"' 'alpha = "^1"'
root root-lsys 'lsys = "=1.0.0"'

. "$S/../serve.sh"
serve "$PORT" "$T/index" "$T/proxy.log" python3 "$S/sparse_proxy.py" "$PORT" "$T/index" || exit 1

# the answer as pac prints it: crates, then "parent child version" edges;
# the expected verdicts as valid/minimal
ctl() {  # <name> <expected> <crates> <edges> [root]
  local name=$1 want=$2 d=$T/$1 got e c=($3) es=($4) r=${5:-root}
  rm -rf "$d"; mkdir -p "$d"
  { echo "root root 1.0.0"; echo "packages (${#c[@]}):"; printf '  %s\n' "${c[@]}" | tr _ ' '
    echo "parent edges (${#es[@]}):"
    for e in "${es[@]}"; do
      set -- ${e//_/ }
      echo "  $1 $2 -> $3($3) $4"
    done; } > "$d/ans.out"
  got=$(bash "$S/../check.sh" cargo "$d/ans.out" "$d/check" "$T/$r/Cargo.toml" |
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
# cargo locks one version per dependency name of a package, whatever the
# cfgs, so its repair re-points split's second edge, whether or not
# something else keeps the version it leaves
ctl split-one VALID/yes 'root_1.0.0 split_1.0.0 wsys_2.0.0' 'root_1.0.0_split_1.0.0 split_1.0.0_wsys_2.0.0' root-split
ctl split-two INVALID/- 'root_1.0.0 split_1.0.0 wsys_1.0.0 wsys_2.0.0' \
  'root_1.0.0_split_1.0.0 split_1.0.0_wsys_1.0.0 split_1.0.0_wsys_2.0.0' root-split
ctl split-held INVALID/- 'root_1.0.0 split_1.0.0 hold_1.0.0 wsys_1.0.0 wsys_2.0.0' \
  'root_1.0.0_split_1.0.0 root_1.0.0_hold_1.0.0 split_1.0.0_wsys_1.0.0 split_1.0.0_wsys_2.0.0 hold_1.0.0_wsys_2.0.0' root-held
# kz's two declarations of zed split as cargo's own fresh lock splits them,
# which cargo's --locked refuses whatever else the lock holds
ctl split-fresh INVALID/- 'root_1.0.0 kz_1.0.0 alpha_1.1.0 zed_1.9.0 zed_2.5.0' \
  'root_1.0.0_kz_1.0.0 root_1.0.0_alpha_1.1.0 kz_1.0.0_zed_1.9.0 kz_1.0.0_zed_2.5.0' root-kz
ctl split-fresh-old INVALID/- 'root_1.0.0 kz_1.0.0 alpha_1.0.0 zed_1.9.0 zed_2.5.0' \
  'root_1.0.0_kz_1.0.0 root_1.0.0_alpha_1.0.0 kz_1.0.0_zed_1.9.0 kz_1.0.0_zed_2.5.0' root-kz
ctl split-none VALID/yes 'root_1.0.0 kz_1.0.0 alpha_1.0.0 zed_1.9.0' \
  'root_1.0.0_kz_1.0.0 root_1.0.0_alpha_1.0.0 kz_1.0.0_zed_1.9.0' root-kz

# cargo failing for want of a registry says nothing of the answer
kill $served; wait $served 2> /dev/null
ctl noproxy ERR/- 'root_1.0.0 alpha_1.1.0' 'root_1.0.0_alpha_1.1.0'

exit $bad
