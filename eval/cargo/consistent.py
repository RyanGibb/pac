#!/usr/bin/env python3
"""Whether pac's answer to a Cargo query is consistent, judged from the
crates.io index rows and the query's manifest alone, as cargo 0.98's
resolver would judge a graph it had built.  Nothing of pac's is read but
its answer, and nothing of cargo's is run: which lock cargo would write
for the same graph is check.py's other question.

The rules, each with the cargo 0.98 source it follows:

  features   The root has every feature it declares, and the default:
             generate-lockfile resolves with CliFeatures::new_all(true)
             (ops/resolve.rs, resolve_with_registry), and
             build_requirements then requires each key of the feature map
             (core/resolver/dep_cache.rs).  Any other package has the
             features every dependency on it asks for, with its default
             where one asks for default features, closed under its feature
             table (Requirements::require_feature, require_value): `dep:x`
             enables the optional dependency x, `x/f` enables x, x's
             feature named x if there is one, and f on x, and `x?/f` asks
             f of x, which the dependency resolver takes to enable x too
             ("Weak features are always activated in the dependency
             resolver", require_value).  An optional dependency not named
             in `dep:` syntax anywhere has an implicit feature of its name
             (core/summary.rs, build_feature_map), and features2 rows are
             merged into features (sources/registry/index/mod.rs).  A
             package's features are the union over everything that asks,
             as the resolver unifies them per package id.  pac's answer
             must list exactly these, and every feature asked for must
             exist (RequirementError::MissingFeature).

  active     A declaration is active when it is not optional or its name
             is enabled, and is a dev-dependency only of the root:
             resolve_features filters `d.is_transitive() || opts.dev_deps`,
             and only the root is resolved with dev units (HasDevUnits::Yes
             in resolve_with_registry, dev_deps: false for dependencies in
             activate_deps_loop).  Targets do not matter: the lock is
             resolved for every platform.  Every active declaration must
             be met by an edge of the answer to a package of its name whose
             version the requirement matches, by the semver crate's rules
             (OptVersionReq::matches in util/semver_ext.rs calls
             VersionReq::matches; semver 1.0.27, eval.rs and parse.rs).
             An edge that no declaration names, active or not, is not the
             answer's to give.

  semver     At most one version of a package in each semver compatibility
             class, the left-most non-zero component (core/resolver/
             types.rs, SemverCompatibility and ActivationsKey;
             RemainingCandidates::next in core/resolver/mod.rs).  The key
             carries the source, so the root, a path package, is apart.

  links      No two packages with one `links` value (ResolverContext::
             flag_activated in core/resolver/context.rs, and
             RemainingCandidates::next).

A package the answer lists that nothing active reaches is judged on the
features pac gives it, and makes the answer not minimal, as does an edge
no active declaration uses.

usage: consistent.py <pac's answer> <Cargo.toml pac was asked>
env: CARGO_INDEX, the index when not repos/crates.io-index
Prints the verdict as JSON: valid (a bool), minimal, and the misses.
"""
import itertools
import json
import os
import re
import sys
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
INDEX = os.environ.get("CARGO_INDEX") or os.path.normpath(HERE + "/../../repos/crates.io-index")


def version(s):
    """semver's Version, build metadata dropped: (major, minor, patch, pre)"""
    core, _, pre = s.split("+", 1)[0].partition("-")
    major, minor, patch = (int(x) for x in core.split("."))
    return major, minor, patch, tuple(pre.split(".")) if pre else ()


def pre_key(pre):
    """semver's Prerelease ordering: a release above any pre-release,
    numeric identifiers numerically and below alphanumeric ones, a longer
    list above its prefix (impls.rs, Ord for Prerelease)"""
    if not pre:
        return (1,)
    return (0, tuple((0, int(i), "") if i.isdigit() else (1, 0, i) for i in pre))


OP = re.compile(r"\s*(=|>=|>|<=|<|~|\^)?\s*")


def requirement(s):
    """semver's VersionReq: comparators (op, major, minor, patch, pre), a
    missing minor or patch None; [] for `*` (parse.rs)"""
    s = s.strip()
    if s in ("*", "x", "X"):
        return []
    out = []
    for part in s.split(","):
        m = OP.match(part)
        op, rest = m.group(1), part[m.end():].strip()
        wild = False
        nums = []
        body, _, pre = rest.split("+", 1)[0].partition("-")
        for x in body.split("."):
            if x in ("*", "x", "X"):
                wild = True
                break
            nums.append(int(x))
        if op is None:
            op = "wild" if wild else "^"
        nums += [None] * (3 - len(nums))
        out.append((op, nums[0], nums[1], nums[2],
                    tuple(pre.split(".")) if pre and nums[2] is not None else ()))
    return out


def comparator(c, v):
    """eval.rs, matches_impl"""
    op, ma, mi, pa, pre = c
    V, Mi, Pa, Pre = v
    exact = V == ma and (mi is None or Mi == mi) and (pa is None or Pa == pa) and Pre == pre

    def greater():
        if V != ma:
            return V > ma
        if mi is None:
            return False
        if Mi != mi:
            return Mi > mi
        if pa is None:
            return False
        if Pa != pa:
            return Pa > pa
        return pre_key(Pre) > pre_key(pre)

    def less():
        if V != ma:
            return V < ma
        if mi is None:
            return False
        if Mi != mi:
            return Mi < mi
        if pa is None:
            return False
        if Pa != pa:
            return Pa < pa
        return pre_key(Pre) < pre_key(pre)

    if op in ("=", "wild"):
        return exact
    if op == ">":
        return greater()
    if op == ">=":
        return exact or greater()
    if op == "<":
        return less()
    if op == "<=":
        return exact or less()
    if op == "~":
        if V != ma or (mi is not None and Mi != mi):
            return False
        if pa is not None and Pa != pa:
            return Pa > pa
        return pre_key(Pre) >= pre_key(pre)
    # caret
    if V != ma:
        return False
    if mi is None:
        return True
    if pa is None:
        return Mi >= mi if ma > 0 else Mi == mi
    if ma > 0:
        if Mi != mi:
            return Mi > mi
        if Pa != pa:
            return Pa > pa
    elif mi > 0:
        if Mi != mi:
            return False
        if Pa != pa:
            return Pa > pa
    elif Mi != mi or Pa != pa:
        return False
    return pre_key(Pre) >= pre_key(pre)


def matches(req, v):
    """eval.rs, matches_req: every comparator, and a pre-release only where
    some comparator names its major.minor.patch with a pre-release"""
    v = version(v)
    if not all(comparator(c, v) for c in req):
        return False
    return not v[3] or any(c[1:4] == v[:3] and c[4] for c in req)


def compat(v):
    """types.rs, SemverCompatibility"""
    major, minor, patch, _ = version(v)
    return ("major", major) if major else ("minor", minor) if minor else ("patch", patch)


def index_path(name):
    n = name.lower()
    if len(n) <= 2:
        return f"{INDEX}/{len(n)}/{n}"
    if len(n) == 3:
        return f"{INDEX}/3/{n[0]}/{n}"
    return f"{INDEX}/{n[:2]}/{n[2:4]}/{n}"


class Summary:
    """a package as the resolver sees it: its declarations, feature map
    and links"""

    def __init__(self, deps, features, links):
        # (name in toml, package, req, kind, optional, default features, features)
        self.deps = deps
        explicit = {v[4:] for vs in features.values() for v in vs if v.startswith("dep:")}
        self.features = {k: list(v) for k, v in features.items()}
        for d in deps:
            if d[4] and d[0] not in features and d[0] not in explicit:
                self.features[d[0]] = ["dep:" + d[0]]
        self.links = links


def from_index(name, vers):
    try:
        with open(index_path(name)) as f:
            rows = [json.loads(l) for l in f if l.strip()]
    except FileNotFoundError:
        return None
    j = next((r for r in rows if r.get("vers") == vers), None)
    if j is None:
        return None
    features = {k: list(v) for k, v in (j.get("features") or {}).items()}
    for k, v in (j.get("features2") or {}).items():
        features.setdefault(k, []).extend(v)
    deps = [(d["name"], d.get("package") or d["name"], d.get("req", "*"), d.get("kind") or "normal",
             bool(d.get("optional")), d.get("default_features", True), tuple(d.get("features") or ()))
            for d in j.get("deps") or []]
    return Summary(deps, features, j.get("links"))


def from_manifest(path):
    with open(path, "rb") as f:
        doc = tomllib.load(f)
    deps = []
    for t in [doc] + list((doc.get("target") or {}).values()):
        for table, kind in (("dependencies", "normal"), ("build-dependencies", "build"),
                            ("dev-dependencies", "dev")):
            for name, d in (t.get(table) or {}).items():
                d = {"version": d} if isinstance(d, str) else d
                deps.append((name, d.get("package") or name, d.get("version", "*"), kind,
                             bool(d.get("optional")),
                             d.get("default-features", d.get("default_features", True)),
                             tuple(d.get("features") or ())))
    pkg = doc["package"]
    return (pkg["name"], pkg["version"]), Summary(deps, doc.get("features") or {}, pkg.get("links"))


def parse_answer(text):
    m = re.search(r"^root (\S+) (\S+)", text, re.M)
    root = (m.group(1), m.group(2)) if m else None
    crates, edges, section = {}, [], None
    for line in text.splitlines():
        if line.startswith("packages ("):
            section = "c"
        elif line.startswith("parent edges ("):
            section = "e"
        elif not line.startswith("  "):
            section = None
        elif section == "c":
            mm = re.match(r"^  (\S+) (\S+)(?: \[(.*)\])?$", line)
            if mm:
                crates[(mm.group(1), mm.group(2))] = set(mm.group(3).split(",")) if mm.group(3) else set()
        elif section == "e":
            mm = re.match(r"^  (\S+) (\S+) -> (\S+)\((\S+)\) (\S+)$", line)
            if mm:
                pn, pv, alias, cn, cv = mm.groups()
                edges.append(((pn, pv), alias, (cn, cv)))
    return root, crates, edges


class Requirements:
    """dep_cache.rs, Requirements: the features a package ends up with and
    the features it asks of each dependency, by name in toml"""

    def __init__(self, s, miss, who):
        self.s, self.miss, self.who = s, miss, who
        self.features, self.deps = set(), {}

    def feature(self, f):
        if "/" in f or f.startswith("dep:"):
            self.value(f)
            return
        if f in self.features:
            return
        if f not in self.s.features:
            self.miss.append(f"{self.who} has no feature {f}")
            return
        self.features.add(f)
        for v in self.s.features[f]:
            self.value(v)

    def value(self, v):
        if "/" in v:
            dep, feat = v.split("/", 1)
            weak = dep.endswith("?")
            dep = dep.rstrip("?")
            if not weak and any(d[0] == dep and d[4] for d in self.s.deps) and dep in self.s.features:
                self.feature(dep)
            self.deps.setdefault(dep, set()).add(feat)
        elif v.startswith("dep:"):
            self.deps.setdefault(v[4:], set())
        else:
            self.feature(v)


def check(answer, manifest):
    root, crates, edges = parse_answer(answer)
    mroot, rsum = from_manifest(manifest)
    miss = []
    if root is None or tuple(root) != mroot:
        return {"valid": None, "minimal": None, "miss": [f"the answer's root is {root}, not {mroot}"]}
    summaries = {}
    for c in crates:
        s = rsum if c == root else from_index(*c)
        if s is None:
            return {"valid": None, "minimal": None, "miss": [f"{c[0]} {c[1]} is not in the index"]}
        summaries[c] = s
    kids = {}
    for p, alias, c in edges:
        kids.setdefault(p, []).append((alias, c))
        if c not in crates:
            miss.append(f"{p[0]} {p[1]} -> {c[0]} {c[1]}, which the answer does not list")

    def active(p, reqs):
        return [d for d in summaries[p].deps
                if (d[3] != "dev" or p == root) and (not d[4] or d[0] in reqs.deps)]

    def serve(p, decls):
        """each declaration's edge: one meeting it, covering as many of p's
        edges of that name as can be, since two declarations of a name may
        each have their own, and be two alike"""
        out = []
        for key, group in itertools.groupby(sorted(decls, key=lambda d: (d[0], d[1])),
                                            key=lambda d: (d[0], d[1])):
            group = list(group)
            cands = [[c for a, c in kids.get(p, []) if a == key[0] and c[0] == key[1]
                      and matches(requirement(d[2]), c[1])] for d in group]
            best = max(itertools.islice(itertools.product(*[cs or [None] for cs in cands]), 4096),
                       key=lambda pick: len({c for c in pick if c}))
            out += zip(group, best)
        return out

    def require(p, want, default, into):
        reqs = Requirements(summaries[p], into, f"{p[0]} {p[1]}")
        for f in sorted(set(summaries[p].features) if p == root else ()) + sorted(want):
            reqs.feature(f)
        if default and "default" in summaries[p].features:
            reqs.feature("default")
        return reqs

    # what each package reached is asked for: features, and its default;
    # a package asked for more is redone, which only grows
    asked = {root: (set(), True)}
    used = set()
    todo = [root]
    while todo:
        p = todo.pop()
        reqs = require(p, *asked[p], [])
        for d, c in serve(p, active(p, reqs)):
            if c is None:
                continue
            used.add((p, d[0], c))
            old = asked.get(c, (set(), False))
            new = (old[0] | reqs.deps.get(d[0], set()) | set(d[6]), old[1] or d[5])
            if c not in asked or new != old:
                asked[c] = new
                todo.append(c)
    for p in sorted(crates):
        reqs = require(p, *asked.get(p, (crates[p], False)), miss)
        if p in asked and reqs.features != crates[p]:
            miss.append(f"{p[0]} {p[1]} has features [{','.join(sorted(crates[p]))}], cargo unifies "
                        f"[{','.join(sorted(reqs.features))}]")
        for d, c in serve(p, active(p, reqs)):
            if c is None:
                miss.append(f"{p[0]} {p[1]} needs {d[1]} {d[2]}"
                            + (f" as {d[0]}" if d[0] != d[1] else "") + ", and no edge meets it")
        for alias, c in kids.get(p, []):
            if not any(d[0] == alias and d[1] == c[0] and matches(requirement(d[2]), c[1])
                       for d in summaries[p].deps):
                miss.append(f"{p[0]} {p[1]} -> {c[0]} {c[1]} as {alias} is no declaration of it")
    classes = {}
    for c in crates:
        if c != root:
            classes.setdefault((c[0], compat(c[1])), []).append(c[1])
    miss += [f"{n} {', '.join(sorted(vs))} are one semver-compatible class"
             for (n, _), vs in sorted(classes.items()) if len(vs) > 1]
    owners = {}
    for c in crates:
        if summaries[c].links:
            owners.setdefault(summaries[c].links, []).append(c)
    miss += [f"{' and '.join(f'{c[0]} {c[1]}' for c in cs)} all link {l}"
             for l, cs in sorted(owners.items()) if len(cs) > 1]
    minimal = set(crates) <= set(asked) and all((p, a, c) in used for p, a, c in edges)
    return {"valid": not miss, "minimal": minimal, "miss": sorted(set(miss))}


def main():
    with open(sys.argv[1]) as f:
        answer = f.read()
    try:
        r = check(answer, sys.argv[2])
    except (ValueError, KeyError, OSError) as e:
        r = {"valid": None, "minimal": None, "miss": [f"unchecked: {e!r}"]}
    print(json.dumps(r, indent=1))


if __name__ == "__main__":
    main()
