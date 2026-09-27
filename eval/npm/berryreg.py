#!/usr/bin/env python3
"""A local registry for Yarn Berry over the packument snapshot.

GET /<name> serves the snapshot's packument, each version's dist pointing
at a tarball here; GET /<name>/-/<file>.tgz serves a tarball made on the
spot from that version's manifest, with an index.js beside it.  Berry
then resolves, fetches and links against the same bytes pac read, and
what a package loads under PnP is read off package.json alone, so no real
tarball is needed.  bin, scripts and directories are dropped from both, as
nothing here runs a package; Berry verifies no registry integrity, only
the checksum it records itself.  The tarball's package.json drops the
entry points, main and exports and the like, as they name files that are
not there.

A name the snapshot lacks is a 404, so a check never reaches the live
registry.  GET /-/pac-serves answers the snapshot directory, which
serve.sh asks to tell this registry from one another run left on the
port.

usage: berryreg.py <port> <snapshot-dir>
"""
import gzip
import http.server
import io
import json
import os
import sys
import tarfile
import threading
import urllib.parse

from tree import escape

SNAP = None
PORT = None
DROP = ("bin", "scripts", "directories", "dist", "_id", "_resolved", "_integrity",
        "_from", "_npmUser", "_npmOperationalInternal", "_hasShrinkwrap", "gitHead")
# the files Berry's built-in compat patches edit (plugin-compat's
# sources/patches, 4.14.1), which a tarball here holds empty: the patches
# are optional, so a hunk that does not match is skipped with a warning,
# where a file that is not there fails the install
PATCHED = {
    "fsevents": ["fsevents.js"],
    "resolve": ["lib/normalize-options.js"],
    "typescript": ["lib/tsc.js", "lib/tsserver.js", "lib/tsserverlibrary.js", "lib/typescript.js",
                   "lib/typescriptServices.js", "lib/typingsInstaller.js",
                   "lib/tsserverlibrary.d.ts", "lib/typescript.d.ts",
                   "lib/typescriptServices.d.ts", "lib/_tsc.js", "lib/_tsserver.js"],
}
LOCK = threading.Lock()
MEMO = {}


def manifest(m):
    return {k: v for k, v in m.items() if k not in DROP}


def base(name):
    return name.rsplit("/", 1)[-1]


def packument(name):
    with LOCK:
        if name in MEMO:
            return MEMO[name]
    path = os.path.join(SNAP, escape(name) + ".json")
    if not os.path.exists(path):
        return None
    with open(path) as f:
        doc = json.load(f)
    vers = {}
    for v, m in (doc.get("versions") or {}).items():
        if not isinstance(m, dict):
            continue
        m = manifest(m)
        m["dist"] = {"tarball": "http://127.0.0.1:%d/%s/-/%s-%s.tgz" % (PORT, name, base(name), v)}
        vers[v] = m
    out = {"name": name, "versions": vers, "dist-tags": doc.get("dist-tags") or {},
           "time": doc.get("time") or {}}
    with LOCK:
        MEMO[name] = out
    return out


def tarball(name, version):
    doc = packument(name)
    m = doc and doc["versions"].get(version)
    if m is None:
        return None
    # entry points name files no tarball here holds, so they go, and
    # require() finds index.js and package.json
    m = {k: v for k, v in m.items()
         if k not in ("dist", "main", "module", "browser", "exports", "imports", "types", "typings")}
    files = [("package.json", json.dumps(m, indent=2).encode()),
             ("index.js", b"module.exports = require('./package.json');\n")]
    files += [(p, b"") for p in PATCHED.get(name, ())]
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w", format=tarfile.USTAR_FORMAT) as t:
        for fn, data in files:
            info = tarfile.TarInfo("package/" + fn)
            info.size, info.mtime, info.mode = len(data), 499162500, 0o644
            t.addfile(info, io.BytesIO(data))
    out = io.BytesIO()
    with gzip.GzipFile(fileobj=out, mode="wb", mtime=0) as g:
        g.write(raw.getvalue())
    return out.getvalue()


class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        path = urllib.parse.unquote(self.path.split("?", 1)[0]).lstrip("/")
        body, ctype = None, "application/json"
        if path == "-/pac-serves":
            body, ctype = os.path.realpath(SNAP).encode(), "text/plain"
        elif "/-/" in path and path.endswith(".tgz"):
            name, fn = path.split("/-/", 1)
            stem = fn[:-len(".tgz")]
            b = base(name) + "-"
            if stem.startswith(b):
                body, ctype = tarball(name, stem[len(b):]), "application/octet-stream"
        else:
            doc = packument(path)
            body = doc and json.dumps(doc).encode()
        if body is None:
            self.send_response(404)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *a):
        pass


class Server(http.server.ThreadingHTTPServer):
    request_queue_size = 512
    daemon_threads = True


if __name__ == "__main__":
    PORT, SNAP = int(sys.argv[1]), sys.argv[2]
    Server(("127.0.0.1", PORT), Handler).serve_forever()
