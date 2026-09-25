#!/usr/bin/env python3
"""A local sparse-registry HTTP server serving repos/crates.io-index
byte-for-byte.

It exists to pin cargo to the same snapshot pac reads, not to change what
either side sees: the [source] replacement in CARGO_HOME/config.toml
points at this server so a measured run cannot drift onto the live
crates.io index between one query and the next.  Nothing is filtered --
cargo's version resolver never sees a target (resolve_with_previous takes
no RustcTargetData), so a [target.'cfg(...)'] row constrains a linux
resolve exactly as an unconditional one does, and pac ignores the cfg the
same way.  Both sides answer about
crates.io as it actually is.

The served config.json still names the real static.crates.io under "dl",
but neither scale.sh nor check.py reaches it: both ask cargo only for a
lockfile, which it resolves from these rows and writes without downloading
a body.  features.py does reach it, for cargo metadata.

/pac-index answers the index directory served, so that a run can tell its
own proxy from one another checkout left on the port.

usage: sparse_proxy.py [port] [index-dir]
"""
import http.server, json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from run_query import INDEX, crate_path  # noqa: E402


class Handler(http.server.BaseHTTPRequestHandler):
    def _send(self, body: bytes, ctype="text/plain"):
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = self.path.split("?", 1)[0].lstrip("/")
        if path == "config.json":
            body = json.dumps(
                {"dl": "https://static.crates.io/crates", "api": "https://crates.io"}
            ).encode()
            self._send(body, "application/json")
            return
        if path == "pac-index":
            self._send(os.path.realpath(self.server.index).encode())
            return
        name = path.split("/")[-1]
        fpath = crate_path(name, self.server.index)
        if not os.path.exists(fpath):
            self.send_response(404)
            self.end_headers()
            return
        with open(fpath, "rb") as f:
            self._send(f.read())

    def log_message(self, fmt, *args):
        pass


if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8991
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", port), Handler)
    srv.index = sys.argv[2] if len(sys.argv) > 2 else INDEX
    srv.serve_forever()
