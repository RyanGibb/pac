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
root root-optf 'opt = { version = "=1.0.0", features = ["fb"] }'
root root-devy 'devy = "=1.0.0"'
root root-kz 'kz = "=1.0.0"' 'alpha = "^1"'
root root-lsys 'lsys = "=1.0.0"'

. "$S/../serve.sh"
serve "$PORT" "$T/index" "$T/proxy.log" python3 "$S/sparse_proxy.py" "$PORT" "$T/index" || exit 1

verdicts() { tail -n 1 | sed -n 's/.* valid=\([A-Z]*\) minimal=\([a-z-]*\) reproduced=\([a-z-]*\)$/\1\/\2\/\3/p'; }
report() {  # <name> <expected> <got>
  printf '%-18s expect %-15s got %s\n' "$1" "$2" "$3"
  [ "$3" = "$2" ] || bad=1
}

# the answer as pac prints it: crates, each name_version or
# name_version_[features], then "parent child version" edges; the expected
# verdicts as valid/minimal/reproduced
ctl() {  # <name> <expected> <crates> <edges> [root]
  local name=$1 want=$2 d=$T/$1 e c=($3) es=($4) r=${5:-root}
  rm -rf "$d"; mkdir -p "$d"
  { echo "root root 1.0.0"; echo "packages (${#c[@]}):"; printf '  %s\n' "${c[@]}" | tr _ ' '
    echo "parent edges (${#es[@]}):"
    for e in "${es[@]}"; do
      set -- ${e//_/ }
      echo "  $1 $2 -> $3($3) $4"
    done; } > "$d/ans.out"
  report "$name" "$want" "$(bash "$S/../check.sh" cargo "$d/ans.out" "$d/check" "$T/$r/Cargo.toml" | verdicts)"
}

# cargo's own fresh lock for a root, as pac would print it
fresh() {  # <name> <expected> <root>
  local d=$T/$1
  rm -rf "$d"; mkdir -p "$d/g"; cp -r "$T/$3/." "$d/g/"
  python3 - "$S" "$d" <<'EOF' || { report "$1" "$2" "cargo failed"; return; }
import os, subprocess, sys
sys.path.insert(0, sys.argv[1])
import run_query
d = sys.argv[2]
subprocess.run(["cargo", "generate-lockfile", "--manifest-path", d + "/g/Cargo.toml"], check=True,
               capture_output=True, env=run_query.write_cargo_config(d + "/cargo-home"))
pkgs, edges = run_query.read_lock(d + "/g/Cargo.lock")
with open(d + "/ans.out", "w") as f:
    f.write("root root 1.0.0\npackages (%d):\n" % len(pkgs))
    f.writelines("  %s %s\n" % p for p in sorted(pkgs))
    f.write("parent edges (%d):\n" % len(edges))
    f.writelines("  %s %s -> %s(%s) %s\n" % (p + (c[0],) + c) for p, c in sorted(edges))
EOF
  report "$1" "$2" "$(bash "$S/../check.sh" cargo "$d/ans.out" "$d/check" "$T/$3/Cargo.toml" | verdicts)"
}

ctl ok VALID/yes/yes 'root_1.0.0 alpha_1.1.0' 'root_1.0.0_alpha_1.1.0'
# older than cargo would pick, and still admitted: cargo keeps it
ctl old VALID/yes/yes 'root_1.0.0 alpha_1.0.0' 'root_1.0.0_alpha_1.0.0'
ctl missing INVALID/-/- 'root_1.0.0' ''
ctl range INVALID/-/- 'root_1.0.0 alpha_2.0.0' 'root_1.0.0_alpha_2.0.0'
# nothing reaches zeta: cargo drops it
ctl extra VALID/no/no 'root_1.0.0 alpha_1.1.0 zeta_2.0.0' 'root_1.0.0_alpha_1.1.0'
# and zeta 1.0.0 needs a beta the answer lacks
ctl extra-broken INVALID/-/- 'root_1.0.0 alpha_1.1.0 zeta_1.0.0' 'root_1.0.0_alpha_1.1.0'
# a package's two declarations of one name, each met by its own version:
# consistent, and cargo, which locks one version per dependency name of a
# package, re-points the second
ctl split-one VALID/yes/yes 'root_1.0.0 split_1.0.0 wsys_2.0.0' 'root_1.0.0_split_1.0.0 split_1.0.0_wsys_2.0.0' root-split
ctl split-two VALID/yes/no 'root_1.0.0 split_1.0.0 wsys_1.0.0 wsys_2.0.0' \
  'root_1.0.0_split_1.0.0 split_1.0.0_wsys_1.0.0 split_1.0.0_wsys_2.0.0' root-split
ctl split-held VALID/yes/no 'root_1.0.0 split_1.0.0 hold_1.0.0 wsys_1.0.0 wsys_2.0.0' \
  'root_1.0.0_split_1.0.0 root_1.0.0_hold_1.0.0 split_1.0.0_wsys_1.0.0 split_1.0.0_wsys_2.0.0 hold_1.0.0_wsys_2.0.0' root-held
# kz's two declarations of zed split as cargo's own fresh lock splits them,
# which cargo's --locked refuses whatever else the lock holds
ctl split-fresh VALID/yes/no 'root_1.0.0 kz_1.0.0 alpha_1.1.0 zed_1.9.0 zed_2.5.0' \
  'root_1.0.0_kz_1.0.0 root_1.0.0_alpha_1.1.0 kz_1.0.0_zed_1.9.0 kz_1.0.0_zed_2.5.0' root-kz
ctl split-fresh-old VALID/yes/no 'root_1.0.0 kz_1.0.0 alpha_1.0.0 zed_1.9.0 zed_2.5.0' \
  'root_1.0.0_kz_1.0.0 root_1.0.0_alpha_1.0.0 kz_1.0.0_zed_1.9.0 kz_1.0.0_zed_2.5.0' root-kz
ctl split-none VALID/yes/yes 'root_1.0.0 kz_1.0.0 alpha_1.0.0 zed_1.9.0' \
  'root_1.0.0_kz_1.0.0 root_1.0.0_alpha_1.0.0 kz_1.0.0_zed_1.9.0' root-kz
fresh kz-cargo VALID/yes/no root-kz
# edges to declarations left inactive: an optional dependency whose feature
# is off, and a dependency's dev-dependency
ctl opt-off VALID/no/no 'root_1.0.0 opt_1.0.0 beta_1.0.0' 'root_1.0.0_opt_1.0.0 opt_1.0.0_beta_1.0.0' root-opt
ctl dev-of-dep VALID/no/no 'root_1.0.0 devy_1.0.0 beta_1.0.0' 'root_1.0.0_devy_1.0.0 devy_1.0.0_beta_1.0.0' root-devy
# the root asks opt for fb, which enables beta and its implicit feature
ctl opt-on VALID/yes/yes 'root_1.0.0 opt_1.0.0_[beta,fb] beta_1.0.0' \
  'root_1.0.0_opt_1.0.0 opt_1.0.0_beta_1.0.0' root-optf
ctl opt-on-unmet INVALID/-/- 'root_1.0.0 opt_1.0.0_[beta,fb]' 'root_1.0.0_opt_1.0.0' root-optf
# features cargo would not unify: fb nothing asks for, fz opt does not have
ctl feat-extra INVALID/-/- 'root_1.0.0 opt_1.0.0_[beta,fb] beta_1.0.0' \
  'root_1.0.0_opt_1.0.0 opt_1.0.0_beta_1.0.0' root-opt
ctl feat-unknown INVALID/-/- 'root_1.0.0 opt_1.0.0_[fz]' 'root_1.0.0_opt_1.0.0' root-opt
ctl feat-short INVALID/-/- 'root_1.0.0 opt_1.0.0_[fb] beta_1.0.0' \
  'root_1.0.0_opt_1.0.0 opt_1.0.0_beta_1.0.0' root-optf
# one version per semver compatibility class, and one owner of links lx
ctl extra-dup INVALID/-/- 'root_1.0.0 alpha_1.1.0 alpha_1.0.0' 'root_1.0.0_alpha_1.1.0'
ctl links-one VALID/yes/yes 'root_1.0.0 lsys_1.0.0' 'root_1.0.0_lsys_1.0.0' root-lsys
ctl extra-links INVALID/-/- 'root_1.0.0 lsys_1.0.0 lsysb_1.0.0' 'root_1.0.0_lsys_1.0.0' root-lsys
# packages nothing reaches judged all the same: an edge outside its range,
# an edge nothing declares
ctl extra-range INVALID/-/- 'root_1.0.0 alpha_1.1.0 hold_1.0.0 wsys_1.0.0 wsys_2.0.0' \
  'root_1.0.0_alpha_1.1.0 hold_1.0.0_wsys_1.0.0'
ctl extra-undeclared INVALID/-/- 'root_1.0.0 alpha_1.1.0 zed_1.0.0 beta_1.0.0' \
  'root_1.0.0_alpha_1.1.0 zed_1.0.0_beta_1.0.0'

# cargo failing for want of a registry says nothing of the answer, and
# leaves only reproduced unknown
kill $served; wait $served 2> /dev/null
ctl noproxy VALID/yes/- 'root_1.0.0 alpha_1.1.0' 'root_1.0.0_alpha_1.1.0'

exit $bad
