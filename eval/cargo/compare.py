#!/usr/bin/env python3
"""Compare one run_goal.py result: version sets and parent-edge sets,
ours vs cargo's.  Pure measurement -- prints the symmetric differences,
does not explain them."""
import argparse, glob, json, sys


def load(path):
    with open(path) as f:
        return json.load(f)


def compare_one(d):
    crate = d["crate"]
    if d.get("cargo") is None or not d["pac"].get("ok"):
        return {"crate": crate, "status": "dropped", "reason": d.get("dropped", "pac failed")}
    if not d["cargo"].get("ok"):
        return {"crate": crate, "status": "dropped",
                "reason": "cargo failed: " + str(d["cargo"].get("stderr", d["cargo"].get("error", "?")))[:300]}

    pac_nodes = {(n, v) for n, v in d["pac"]["crates"]}
    cargo_nodes = {(n, v) for n, v in d["cargo"]["crates"]}
    ours_only_nodes = pac_nodes - cargo_nodes
    cargo_only_nodes = cargo_nodes - pac_nodes

    pac_edges = {(dn, dv, tn, tv) for dn, dv, _alias, tn, tv in d["pac"]["edges"]}
    cargo_edges = {(dn, dv, tn, tv) for dn, dv, tn, tv in d["cargo"]["edges"]}
    ours_only_edges = pac_edges - cargo_edges
    cargo_only_edges = cargo_edges - pac_edges

    return {
        "crate": crate,
        "status": "exact" if not ours_only_nodes and not cargo_only_nodes else "diff",
        "root_rust_version": d.get("root_rust_version"),
        "pac_wall": d["pac"].get("wall"),
        "cargo_wall": d["cargo"].get("wall"),
        "pac_nodes": len(pac_nodes),
        "cargo_nodes": len(cargo_nodes),
        "nodes_ours_only": sorted(ours_only_nodes),
        "nodes_cargo_only": sorted(cargo_only_nodes),
        "pac_edges": len(pac_edges),
        "cargo_edges": len(cargo_edges),
        "edges_ours_only": sorted(ours_only_edges),
        "edges_cargo_only": sorted(cargo_only_edges),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    paths = []
    for pat in args.files:
        paths += glob.glob(pat)
    paths = sorted(set(paths))

    results = [compare_one(load(p)) for p in paths]

    if args.json:
        print(json.dumps(results, indent=1))
        return

    n_exact = sum(1 for r in results if r["status"] == "exact")
    n_diff = sum(1 for r in results if r["status"] == "diff")
    n_dropped = sum(1 for r in results if r["status"] == "dropped")
    print(f"goals: {len(results)}  exact-nodes: {n_exact}  diff-nodes: {n_diff}  dropped: {n_dropped}")
    print()
    for r in results:
        if r["status"] == "dropped":
            print(f"{r['crate']:30s} DROPPED  {r['reason']}")
            continue
        print(f"{r['crate']:30s} nodes ours={r['pac_nodes']:4d} cargo={r['cargo_nodes']:4d} "
              f"ours-only={len(r['nodes_ours_only']):3d} cargo-only={len(r['nodes_cargo_only']):3d}  "
              f"edges ours={r['pac_edges']:4d} cargo={r['cargo_edges']:4d} "
              f"ours-only={len(r['edges_ours_only']):3d} cargo-only={len(r['edges_cargo_only']):3d}  "
              f"wall pac={r['pac_wall']:.2f}s cargo={r['cargo_wall']:.2f}s"
              + (f"  rustv={r['root_rust_version']}" if r['root_rust_version'] else ""))
        if r["nodes_ours_only"]:
            print(f"    nodes ours-only:  {r['nodes_ours_only']}")
        if r["nodes_cargo_only"]:
            print(f"    nodes cargo-only: {r['nodes_cargo_only']}")
        if r["edges_ours_only"]:
            print(f"    edges ours-only:  {r['edges_ours_only']}")
        if r["edges_cargo_only"]:
            print(f"    edges cargo-only: {r['edges_cargo_only']}")


if __name__ == "__main__":
    main()
