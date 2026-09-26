#!/usr/bin/env python3
"""Fail when a comment in lib/, bin/, eval/ or test/ cites a Rocq name that
theories/ does not define.

A comment cites a Rocq name when it writes a qualified path whose head is a
theories/ module or a driver's alias of one (Lookup.versions_lookupOrig,
Red.versions, DMA.Deb.vtMatchb), a name the Rocq naming scheme alone produces
(snake prefix, camel suffix: dependees_reduceDepsInert), a name after
Lemma/Theorem/Definition, or a file X.v.  A trailing * is a prefix glob and
must match at least one name.  Only comments are read, so the extracted code
itself is checked by the compiler, not here.

usage: check-citations.py [ROOT]   (ROOT defaults to the script's parent's parent)
"""
import os
import re
import sys

ROOT = os.path.abspath(sys.argv[1] if len(sys.argv) > 1
                       else os.path.join(os.path.dirname(__file__), ".."))
THEORIES = os.path.join(ROOT, "theories")
SCAN = ["lib", "bin", "eval", "test"]
# Harness data, not prose.
SKIP_DIRS = {"baseline", "_build", "node_modules"}

DECL = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Program|Polymorphic)\s+)*"
    r"(?:Definition|Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example|"
    r"Fixpoint|CoFixpoint|Inductive|CoInductive|Variant|Record|Structure|Class|"
    r"Instance|Let|Parameter|Parameters|Axiom|Hypothesis|Variable|Variables|"
    r"Notation|Ltac|Module(?:\s+Type)?|Declare\s+Module|Section|Scheme|"
    r"Function|Equations)\s+([A-Za-z_][\w']*)")
MUTUAL = re.compile(r"^\s*with\s+([A-Za-z_][\w']*)")
CTOR = re.compile(r"(?:^|:=|\|)\s*\|?\s*([A-Z][\w']*)\s*(?::|\||$|\()")
FIELD = re.compile(r"[{;]\s*([A-Za-z_][\w']*)\s*:(?!=)")


def rocq_names():
    names, modules, files, byfile, includes = set(), set(), set(), {}, {}
    for f in sorted(os.listdir(THEORIES)):
        if not f.endswith(".v"):
            continue
        files.add(f[:-2])
        modules.add(f[:-2])
        text = strip_rocq_comments(open(os.path.join(THEORIES, f)).read())
        in_ind = False
        mine = byfile.setdefault(f[:-2], set())
        before = set(names)
        names = set()
        incl, modal = [], {}
        for line in text.splitlines():
            m = DECL.match(line)
            if m:
                names.add(m.group(1))
                kw = line.split()[0]
                if "Module" in line.split(m.group(1))[0]:
                    modules.add(m.group(1))
                in_ind = kw in ("Inductive", "CoInductive", "Variant",
                                "Record", "Structure", "Class")
            m = re.match(r"^\s*Include\s+([A-Z]\w*)", line)
            if m:
                incl.append(m.group(1))
            m = re.match(r"^\s*(?:Declare\s+)?Module\s+([A-Z]\w*)\s*(?:<:[^:]*)?:=\s*([A-Z]\w*)", line)
            if m:
                modal[m.group(1)] = m.group(2)
            m = MUTUAL.match(line)
            if m:
                names.add(m.group(1))
            if in_ind:
                names.update(CTOR.findall(line))
                names.update(FIELD.findall(line))
                if line.rstrip().endswith("."):
                    in_ind = False
        mine |= names
        names |= before
        # Include Sv, where Module Sv := Semver.Make ...: Semver's names are Npm's.
        includes[f[:-2]] = [modal.get(i, i) for i in incl]
    for _ in range(len(byfile)):
        for f, inc in includes.items():
            for g in inc:
                byfile[f] |= byfile.get(g, set())
    return names, modules, files, byfile


def strip_rocq_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1; i += 2
        elif depth and s.startswith("*)", i):
            depth -= 1; i += 2
        else:
            if not depth:
                out.append(s[i])
            elif s[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def ocaml_comments(s):
    """(line, text) for each line of each (* *) comment, nesting honoured,
    string literals outside comments skipped."""
    depth, i, line, buf, start = 0, 0, 1, [], 1
    while i < len(s):
        c = s[i]
        if not depth and c == '"':
            i += 1
            while i < len(s) and s[i] != '"':
                if s[i] == "\\":
                    i += 1
                if i < len(s) and s[i] == "\n":
                    line += 1
                i += 1
            i += 1
            continue
        if not depth and c == "'" and s.startswith("'\"'", i):
            i += 3
            continue
        if s.startswith("(*", i):
            if not depth:
                buf, start = [], line
            depth += 1; i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; i += 2
            if not depth:
                for k, t in enumerate("".join(buf).split("\n")):
                    yield start + k, t
            continue
        if c == "\n":
            line += 1
        if depth:
            buf.append(c)
        i += 1


def hash_comments(s, docstrings):
    in_doc = None
    for n, l in enumerate(s.splitlines(), 1):
        if docstrings:
            if in_doc:
                yield n, l
                if in_doc in l:
                    in_doc = None
                continue
            m = re.search(r'("""|\'\'\')', l)
            if m:
                q = m.group(1)
                yield n, l[m.end():]
                if q not in l[m.end():]:
                    in_doc = q
                continue
        m = re.search(r"(?:^|\s)#(?!!)(.*)", l)
        if m:
            yield n, m.group(1)


def js_comments(s):
    for n, t in ocaml_like(s, "/*", "*/"):
        yield n, t
    for n, l in enumerate(s.splitlines(), 1):
        m = re.search(r"(?:^|\s)//(.*)", l)
        if m:
            yield n, m.group(1)


def ocaml_like(s, o, c):
    n, i = 1, 0
    while True:
        j = s.find(o, i)
        if j < 0:
            return
        n += s.count("\n", i, j)
        k = s.find(c, j + 2)
        k = len(s) if k < 0 else k
        for d, t in enumerate(s[j + 2:k].split("\n")):
            yield n + d, t
        n += s.count("\n", j, k)
        i = k + 2


def cram_prose(s):
    for n, l in enumerate(s.splitlines(), 1):
        if l and not l.startswith("  "):
            yield n, l


def dune_comments(s):
    for n, l in enumerate(s.splitlines(), 1):
        if ";" in l:
            yield n, l.split(";", 1)[1]


def comments(path, s):
    base = os.path.basename(path)
    if base.endswith((".ml", ".mli")):
        return ocaml_comments(s)
    if base.endswith(".py"):
        return hash_comments(s, True)
    if base.endswith((".sh", ".jq")) or s.startswith("#!"):
        return hash_comments(s, False)
    if base.endswith(".js"):
        return js_comments(s)
    if base.endswith(".t") or path.endswith(".t/run.t"):
        return cram_prose(s)
    if base == "dune":
        return dune_comments(s)
    if base.endswith((".md", ".org", ".txt")) and "queries" not in base:
        return enumerate(s.splitlines(), 1)
    return iter(())


def aliases(prefixes, files):
    """Driver-side module aliases of theories/ modules (module DMA =
    E.DebianMA), each mapped to the theories/ file it lands in, if one."""
    out = {}
    pat = re.compile(r"\bmodule\s+([A-Z]\w*)\s*=\s*([A-Z][\w.]*)")
    changed = True
    srcs = []
    for top in ("lib", "bin"):
        for d, _, fs in os.walk(os.path.join(ROOT, top)):
            srcs += [os.path.join(d, f) for f in fs if f.endswith(".ml")]
    pairs = []
    for f in srcs:
        pairs += pat.findall(open(f).read())
    known = set(prefixes) | {"Pac"}
    while changed:
        changed = False
        for a, rhs in pairs:
            if a not in known and rhs.split(".")[0] in known:
                known.add(a); changed = True
                out[a] = next((out.get(c) or c for c in rhs.split(".")
                               if c in files or out.get(c)), None)
    return out


def main():
    names, modules, files, byfile = rocq_names()
    # Short or generic Rocq module names (C, T, Version) collide with OCaml's;
    # only distinctive ones anchor a qualified citation.
    OCAML = {"List", "Option", "Hashtbl", "String", "Map", "Set", "Array",
             "Printf", "Format", "Cmd", "Arg", "Seq", "Buffer", "Sys", "Fun",
             "Int", "Char", "Bytes", "Result", "Filename", "In_channel"}
    heads = {m for m in modules if len(m) >= 3 and m not in OCAML}
    alias = aliases(heads, files)
    heads |= set(alias)
    heads -= OCAML

    def home(pre):
        """The theories/ file a qualified path names, if its head fixes one."""
        h = pre.split(".")[0]
        return h if h in files else alias.get(h)

    qual = re.compile(r"\b((?:[A-Z][\w']*\.)+)([A-Za-z_][\w']*\*?)")
    scheme = re.compile(r"\b([a-z][a-z0-9]*(?:_[a-z0-9]+)*_[a-z][a-z0-9]*[A-Z][\w']*\*?)")
    keyword = re.compile(r"\b(?:[Ll]emma|[Tt]heorem|[Cc]orollary|[Dd]efinition|Fixpoint)s?\s+"
                         r"[`\[]?([A-Za-z_][\w']*[_A-Z][\w']*\*?)")
    vfile = re.compile(r"\b(?:theories/)?([A-Z]\w*)\.v\b(?![\w.])")

    # Foo.v, Cargo.toml: files, not definitions.
    EXTS = {"v", "vo", "ml", "mli", "py", "sh", "t", "toml", "lock", "json",
            "txt", "org", "md", "js"}

    def exists(n, pool=names):
        if n.endswith("*"):
            return any(x.startswith(n[:-1]) for x in pool)
        return n in pool

    bad = 0
    for top in SCAN:
        for d, ds, fs in os.walk(os.path.join(ROOT, top)):
            ds[:] = [x for x in ds if x not in SKIP_DIRS]
            for f in sorted(fs):
                p = os.path.join(d, f)
                try:
                    s = open(p, encoding="utf-8").read()
                except (UnicodeDecodeError, OSError):
                    continue
                rel = os.path.relpath(p, ROOT)
                for n, t in comments(p, s):
                    cited, seen = [], set()
                    for pre, last in qual.findall(t):
                        last = re.sub(r"'s$", "", last)
                        if last in EXTS or pre.split(".")[0] not in heads:
                            continue
                        seen.add(last)
                        f = home(pre)
                        if f and not exists(last, byfile[f]):
                            where = f"{f}.v" if exists(last) else "theories/"
                            print(f"{rel}:{n}: {pre + last}: not defined in {where}")
                            bad += 1
                        elif not exists(last):
                            print(f"{rel}:{n}: {pre + last}: not defined in theories/")
                            bad += 1
                    for m in scheme.findall(t) + keyword.findall(t):
                        if m not in seen and not exists(m):
                            seen.add(m)
                            print(f"{rel}:{n}: {m}: not defined in theories/")
                            bad += 1
                    for m in vfile.findall(t):
                        if m not in files:
                            print(f"{rel}:{n}: {m}.v: no such file in theories/")
                            bad += 1
    if bad:
        print(f"FAIL: {bad} citation(s) of Rocq names theories/ lacks")
        sys.exit(1)


if __name__ == "__main__":
    main()
