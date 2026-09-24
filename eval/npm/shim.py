#!/usr/bin/env python3
"""A local npm registry that serves the packument snapshot verbatim.

The snapshot is a directory of registry documents named as the registry
names them, `/` escaped to `%2F`, which is also the shape `pac npm
--cache` reads, so both sides are answering from the same bytes.  GET
/<name> returns that file unchanged, and with --frozen a name the
snapshot does not hold is a 404 rather than a fetch, which is what keeps
a measured run off the live registry.

--fill is the seeding mode used before a sweep: a miss is fetched once
into the snapshot directory, so the snapshot ends up closed over whatever
npm asked for and a later --frozen run answers everything from disk.
Misses are appended to the file named by --log either way.

`npm install --package-lock-only` asks for the tarball of exactly those
versions whose manifest declares bundleDependencies or a shrinkwrap,
because it takes that part of the tree from inside the tarball rather
than resolving it.  GET /<name>/-/<file>.tgz is answered from tarballs/
beside the snapshot directory, frozen and filled as packuments are.  npm
asks here although dist.tarball names registry.npmjs.org, because pacote
rewrites that host to the configured registry.

usage: shim.py <port> <snapshot-dir> [--frozen|--fill] [--log FILE]
"""
import http.server
import os
import re
import subprocess
import sys
import threading
import urllib.parse

SNAP = None
TARBALLS = None
FILL = False
LOG = None
TARBALL = re.compile(r"^(@[^/]+/)?[^/]+/-/[^/]+\.tgz$")


def escape(name):
    return name.replace("/", "%2F")


def fetch(url, path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    # concurrent asks for one name are normal, so the scratch file is
    # per-request rather than per-name
    tmp = "%s.%d.tmp" % (path, os.getpid() ^ threading.get_ident())
    r = subprocess.run(["curl", "-fsSL", url, "-o", tmp], capture_output=True)
    if r.returncode != 0:
        if os.path.exists(tmp):
            os.unlink(tmp)
        return False
    os.rename(tmp, path)
    return True


class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        raw = self.path.split("?", 1)[0].lstrip("/")
        name = urllib.parse.unquote(raw)
        if not name or name.startswith("-") or ".." in name.split("/"):
            self.send_response(404)
            self.end_headers()
            return
        up = "https://registry.npmjs.org/"
        if TARBALL.match(name):
            path = os.path.join(TARBALLS, escape(name))
            up += urllib.parse.quote(name, safe="/@.-_")
            ctype = "application/octet-stream"
        else:
            path = os.path.join(SNAP, escape(name) + ".json")
            up += urllib.parse.quote(escape(name), safe="%@.-_")
            ctype = "application/json"
        if not os.path.exists(path):
            if LOG:
                with open(LOG, "a") as f:
                    f.write(name + "\n")
            if not (FILL and fetch(up, path)):
                self.send_response(404)
                self.end_headers()
                return
        with open(path, "rb") as f:
            body = f.read()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, fmt, *args):
        pass


class Server(http.server.ThreadingHTTPServer):
    # a sweep's parallel npm processes at a dozen sockets each overrun the
    # default backlog of 5, and a dropped SYN costs npm a retry second
    request_queue_size = 1024
    daemon_threads = True


if __name__ == "__main__":
    port = int(sys.argv[1])
    SNAP = os.path.abspath(sys.argv[2])
    TARBALLS = os.path.join(os.path.dirname(SNAP), "tarballs")
    args = sys.argv[3:]
    FILL = "--fill" in args
    if "--log" in args:
        LOG = args[args.index("--log") + 1]
    Server(("127.0.0.1", port), Handler).serve_forever()
