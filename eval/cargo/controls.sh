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
# and lsysb both linking lx; cya and cyb needing each other, cyc and cyd
# through a build-dependency, cye and cyf through a dev-dependency; fsp
# asking fsq for fsr/f, fdp asking it for dep:fsr, and fep asking fsr for
# the empty feature; fcy's feature a including itself; and rows cargo reads
# as invalid: ivf's feature naming nothing, ivd's optional
# dev-dependency, ivr's and ivq's requirements, ivt's target, ivv's
# version, and rows off the index-row schema: mdeps without deps, mck
# without cksum, onul's null optional, rvx's pre-release rust_version,
# regx's registry, artx's artifact, fstr's feature a string, nreq's
# dependency without req; rvok's rust_version and pubtime, which cargo
# reads; and rows turning on a Unicode class Python and cargo may disagree
# on: tg1's and tg2's targets, alphanumeric to Rust and not to Python, and
# fo2's feature, U+1C89 being newer than Python's tables
rm -rf "$T/index"
python3 - "$T/index" <<'EOF'
import hashlib, json, os, sys
T = sys.argv[1]
DROP = object()
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
        "lsysb": [("1.0.0", [], {}, "lx")],
        "cya": [("1.0.0", [{"name": "cyb", "req": "^1"}])],
        "cyb": [("1.0.0", [{"name": "cya", "req": "^1"}])],
        "cyc": [("1.0.0", [{"name": "cyd", "req": "^1", "kind": "build"}])],
        "cyd": [("1.0.0", [{"name": "cyc", "req": "^1"}])],
        "cye": [("1.0.0", [{"name": "cyf", "req": "^1"}])],
        "cyf": [("1.0.0", [{"name": "cye", "req": "^1", "kind": "dev"}])],
        "fsr": [("1.0.0", [], {"f": []})],
        "fsq": [("1.0.0", [{"name": "fsr", "req": "^1", "optional": True}])],
        "fsp": [("1.0.0", [{"name": "fsq", "req": "^1", "features": ["fsr/f"]}])],
        "fdp": [("1.0.0", [{"name": "fsq", "req": "^1", "features": ["dep:fsr"]}])],
        "fep": [("1.0.0", [{"name": "fsr", "req": "^1", "features": [""]}])],
        "fcy": [("1.0.0", [], {"a": ["a"]})],
        "ivf": [("1.0.0", [], {"extra": ["nope"]})],
        "ivd": [("1.0.0", [{"name": "beta", "req": "^1", "kind": "dev", "optional": True}],
                 {"b": ["dep:beta"]})],
        "ivr": [("1.0.0", [{"name": "beta", "req": "1.0.0.0"}])],
        "ivq": [("1.0.0", [{"name": "beta", "req": "^^1", "kind": "dev"}])],
        "ivt": [("1.0.0", [{"name": "beta", "req": "^1",
                            "target": 'and(cfg(unix), not(target_os = "linux"))'}])],
        "ivv": [("1.0.0-01", [])],
        "mdeps": [("1.0.0", [], {}, None, {"deps": DROP})],
        "mck": [("1.0.0", [], {}, None, {"cksum": DROP})],
        "onul": [("1.0.0", [{"name": "beta", "req": "^1", "optional": None}])],
        "rvx": [("1.0.0", [], {}, None, {"rust_version": "1.70.0-nightly"})],
        "regx": [("1.0.0", [{"name": "beta", "req": "^1", "registry": "not a url"}])],
        "artx": [("1.0.0", [{"name": "beta", "req": "^1", "artifact": ["nonsense"]}])],
        "fstr": [("1.0.0", [], {"a": ""})],
        "nreq": [("1.0.0", [{"name": "beta"}])],
        "rvok": [("1.0.0", [], {}, None, {"rust_version": "1.70", "pubtime": "2025-11-12T19:30:12Z"})],
        "tg1": [("1.0.0", [{"name": "beta", "req": "^1", "target": "Ⓐ"}])],
        "tg2": [("1.0.0", [{"name": "beta", "req": "^1", "target": "xः"}])],
        "fo2": [("1.0.0", [], {"aᲉ": []})]}
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
            if len(more) > 1 and more[1]:
                row["links"] = more[1]
            if len(more) > 2:
                row.update(more[2])
            f.write(json.dumps({k: x for k, x in row.items() if x is not DROP}) + "\n")
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
root root-cya 'cya = "^1"'
root root-cyc 'cyc = "^1"'
root root-cye 'cye = "^1"'
root root-fsp 'fsp = "^1"'
root root-fdp 'fdp = "^1"'
root root-fep 'fep = "^1"'
root root-fcy 'fcy = { version = "=1.0.0", features = ["a"] }'
root root-ivf 'ivf = "=1.0.0"'
root root-ivd 'ivd = "=1.0.0"'
root root-ivr 'ivr = "=1.0.0"'
root root-ivq 'ivq = "=1.0.0"'
root root-ivt 'ivt = "=1.0.0"'
root root-ivv 'ivv = "^1.0.0-0"'
for n in mdeps mck onul rvx regx artx fstr nreq rvok tg1 tg2 fo2; do root root-$n "$n = \"^1\""; done

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
# a cycle through normal or build edges, which cargo refuses whatever else
# it could pick; a dev-dependency of a dependency is no edge
ctl cycle INVALID/-/- 'root_1.0.0 cya_1.0.0 cyb_1.0.0' \
  'root_1.0.0_cya_1.0.0 cya_1.0.0_cyb_1.0.0 cyb_1.0.0_cya_1.0.0' root-cya
ctl cycle-build INVALID/-/- 'root_1.0.0 cyc_1.0.0 cyd_1.0.0' \
  'root_1.0.0_cyc_1.0.0 cyc_1.0.0_cyd_1.0.0 cyd_1.0.0_cyc_1.0.0' root-cyc
ctl cycle-dev VALID/no/no 'root_1.0.0 cye_1.0.0 cyf_1.0.0' \
  'root_1.0.0_cye_1.0.0 cye_1.0.0_cyf_1.0.0 cyf_1.0.0_cye_1.0.0' root-cye
# a dependency's features are names: fsq has no feature fsr/f or dep:fsr,
# and the empty one is dropped
ctl depfeat-slash INVALID/-/- 'root_1.0.0 fsp_1.0.0 fsq_1.0.0_[fsr] fsr_1.0.0_[f]' \
  'root_1.0.0_fsp_1.0.0 fsp_1.0.0_fsq_1.0.0 fsq_1.0.0_fsr_1.0.0' root-fsp
ctl depfeat-dep INVALID/-/- 'root_1.0.0 fdp_1.0.0 fsq_1.0.0 fsr_1.0.0' \
  'root_1.0.0_fdp_1.0.0 fdp_1.0.0_fsq_1.0.0 fsq_1.0.0_fsr_1.0.0' root-fdp
ctl depfeat-empty VALID/yes/yes 'root_1.0.0 fep_1.0.0 fsr_1.0.0' \
  'root_1.0.0_fep_1.0.0 fep_1.0.0_fsr_1.0.0' root-fep
ctl feat-selfcycle INVALID/-/- 'root_1.0.0 fcy_1.0.0_[a]' 'root_1.0.0_fcy_1.0.0' root-fcy
# rows cargo reads as invalid, which it never selects
ctl invalid-feature INVALID/-/- 'root_1.0.0 ivf_1.0.0' 'root_1.0.0_ivf_1.0.0' root-ivf
ctl invalid-optdev INVALID/-/- 'root_1.0.0 ivd_1.0.0' 'root_1.0.0_ivd_1.0.0' root-ivd
ctl invalid-req INVALID/-/- 'root_1.0.0 ivr_1.0.0 beta_1.0.0' \
  'root_1.0.0_ivr_1.0.0 ivr_1.0.0_beta_1.0.0' root-ivr
ctl invalid-req-dev INVALID/-/- 'root_1.0.0 ivq_1.0.0' 'root_1.0.0_ivq_1.0.0' root-ivq
ctl invalid-target INVALID/-/- 'root_1.0.0 ivt_1.0.0 beta_1.0.0' \
  'root_1.0.0_ivt_1.0.0 ivt_1.0.0_beta_1.0.0' root-ivt
ctl invalid-vers INVALID/-/- 'root_1.0.0 ivv_1.0.0-01' 'root_1.0.0_ivv_1.0.0-01' root-ivv
for n in mdeps mck rvx fstr; do
  ctl schema-$n INVALID/-/- "root_1.0.0 ${n}_1.0.0" "root_1.0.0_${n}_1.0.0" root-$n
done
for n in onul regx artx nreq; do
  ctl schema-$n INVALID/-/- "root_1.0.0 ${n}_1.0.0 beta_1.0.0" \
    "root_1.0.0_${n}_1.0.0 ${n}_1.0.0_beta_1.0.0" root-$n
done
ctl schema-rvok VALID/yes/yes 'root_1.0.0 rvok_1.0.0' 'root_1.0.0_rvok_1.0.0' root-rvok
# the check cannot tell what cargo makes of these, and says so
for n in tg1 tg2; do
  ctl unicode-$n ERR/-/- "root_1.0.0 ${n}_1.0.0 beta_1.0.0" \
    "root_1.0.0_${n}_1.0.0 ${n}_1.0.0_beta_1.0.0" root-$n
done
ctl unicode-fo2 ERR/-/- 'root_1.0.0 fo2_1.0.0' 'root_1.0.0_fo2_1.0.0' root-fo2

# cargo failing for want of a registry says nothing of the answer, and
# leaves only reproduced unknown
kill $served; wait $served 2> /dev/null
ctl noproxy VALID/yes/- 'root_1.0.0 alpha_1.1.0' 'root_1.0.0_alpha_1.1.0'

exit $bad
