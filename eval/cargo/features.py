#!/usr/bin/env python3
"""Compare pac's feature set for each crate in the answer with cargo's.

cargo has two feature answers.  `cargo metadata` lists, per resolved
package, the features its version resolver activated in reaching the lock,
which is the set pac's answer carries; `cargo tree -e features` shows the
build view cargo derives from that lock afterwards, per compilation unit.
This compares against metadata's lists.

It is kept out of scale.sh because metadata needs every resolved package's
manifest, so unlike the rest of the harness it downloads crate sources into
CARGO_HOME: about 6 GB over 329 queries, once.

usage: features.py <crate>...    in run_query.py's environment, with
       sparse_proxy.py serving on PORT (default 8991)
"""
import json, os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_query


def compare(crate):
    pac, root, _rustv, patched = run_query.ask_pac(crate)
    if not pac["ok"]:
        return "pac failed"
    cargo = run_query.run_cargo(*root, patched)
    if not cargo["ok"]:
        return "cargo failed"
    # every feature, as generate-lockfile resolves, so metadata's resolve is
    # the lock run_cargo has just written
    p = subprocess.run(["cargo", "metadata", "--format-version", "1", "--all-features",
                        "--manifest-path", f"{run_query.WORK}/{root[0]}/Cargo.toml"],
                       capture_output=True, text=True, env=run_query.write_cargo_config())
    if p.returncode:
        return "metadata failed: " + p.stderr.strip()[-200:]
    md = json.loads(p.stdout)
    ids = {q["id"]: (q["name"], q["version"]) for q in md["packages"]}
    theirs = {ids[n["id"]]: set(n["features"]) for n in md["resolve"]["nodes"]}
    ours = {tuple(k.rsplit("@", 1)): set(fs) for k, fs in pac["feats"].items()}
    both = sorted(ours.keys() & theirs.keys())
    return both, [(c, sorted(ours[c] - theirs[c]), sorted(theirs[c] - ours[c])) for c in both if ours[c] != theirs[c]]


run_query.check_toolchain()
total = same = queries = 0
for crate in sys.argv[1:]:
    r = compare(crate)
    if isinstance(r, str):
        print("%-30s DROPPED %s" % (crate, r))
        continue
    both, diffs = r
    total, same, queries = total + len(both), same + len(both) - len(diffs), queries + (not diffs)
    print("%-30s crates=%d differing=%d" % (crate, len(both), len(diffs)))
    for (n, v), o, t in diffs[:8]:
        print("    %s@%s ours-only=%s cargo-only=%s" % (n, v, ",".join(o) or "-", ",".join(t) or "-"))
print("TOTAL crate versions compared=%d same=%d; queries matching in full=%d" % (total, same, queries))
