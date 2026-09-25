#!/usr/bin/env python3
"""A local sparse-registry HTTP server serving repos/crates.io-index
byte-for-byte.

It exists to pin cargo to the same snapshot pac reads, not to change what
either side sees: the [source] replacement in CARGO_HOME/config.toml
points at this server so a measured run cannot drift onto the live
crates.io index between one query and the next.  Nothing is filtered --
cargo's version resolver never sees a target (resolve_with_previous takes
no RustcTargetData), so a [target.'cfg(...)'] row constrains a linux
resolve exactly as an unconditional one does, and pac's slotActive
(Cargo.v) ignores the cfg the same way.  Both sides answer about
crates.io as it actually is.

The served config.json still names the real static.crates.io under "dl",
but neither scale.sh nor valid.sh reaches it: both ask cargo only for a
lockfile, which it resolves from these rows and writes without downloading
a body.  features.py does reach it, for cargo metadata.
"""
import http.server, json, os, sys

INDEX = os.path.normpath(os.path.dirname(os.path.abspath(__file__)) + "/../../repos/crates.io-index")


def crate_path(name):
    n = name.lower()
    l = len(n)
    if l == 1:
        return f"{INDEX}/1/{n}"
    if l == 2:
        return f"{INDEX}/2/{n}"
    if l == 3:
        return f"{INDEX}/3/{n[0]}/{n}"
    return f"{INDEX}/{n[0:2]}/{n[2:4]}/{n}"


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
        name = path.split("/")[-1]
        fpath = crate_path(name)
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
    srv.serve_forever()
