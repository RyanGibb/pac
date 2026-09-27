// berryprobe.cjs <expect.json>, run under node -r ./.pnp.cjs: whether each
// edge of our answer loads, through PnP's resolver, the copy the answer says.
// From the project root, each copy's rows are resolved as require() would
// from inside it, and each peer it declares is checked against what its
// depender offers in the answer: the depender's own copy of the name, else
// what the depender's own peer loads where it peers on the name too, else
// the depender itself where it has the name, else nothing.  Every PnP
// virtual instance is walked, one per path.  Prints a JSON summary.
const fs = require("fs");
const path = require("path");
const { createRequire } = require("module");

const E = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
const root = process.cwd();
const manifest = (dir) => JSON.parse(fs.readFileSync(path.join(dir, "package.json"), "utf8"));

function locate(from, name) {
  const req = createRequire(path.join(from, "__probe__.js"));
  try {
    return { dir: path.dirname(req.resolve(name + "/package.json")) };
  } catch (e) {}
  try {
    const p = req.resolve(name);
    for (let d = path.dirname(p); d !== path.dirname(d); d = path.dirname(d)) {
      try {
        if (manifest(d).name) return { dir: d };
      } catch (e) {}
    }
  } catch (e) {
    return { err: e.code || String(e).slice(0, 80) };
  }
  return { err: "NOPKG" };
}

const out = { copies: 0, edges: 0, ok: 0, wrong: [], unloaded: [], disabled: [], peerWrong: [], peerMissing: [], fallback: [] };
const cnt = { wrong: 0, unloaded: 0, disabled: 0, peerWrong: 0, peerMissing: 0, fallback: 0 };
const push = (k, x) => {
  cnt[k]++;
  if (out[k].length < 20) out[k].push(x);
};
const same = (dir, id) => {
  const m = manifest(dir);
  return m.name === E[id].name && m.version === E[id].version;
};
const seen = new Set();
const queue = [{ dir: root, id: "", ctx: {} }];
while (queue.length) {
  const { dir, id, ctx } = queue.shift();
  if (seen.has(dir)) continue;
  seen.add(dir);
  out.copies++;
  const n = E[id];
  for (const [p, optional] of Object.entries(n.peers)) {
    const exp = ctx[p];
    const r = locate(dir, p);
    out.edges++;
    if (exp === undefined || exp === null) {
      if (r.dir) push("fallback", `${id} peer ${p} loads ${manifest(r.dir).name}@${manifest(r.dir).version}, the answer offers none${optional ? " (optional)" : ""}`);
      else out.ok++;
    } else if (!r.dir) push("peerMissing", `${id} peer ${p}: ${r.err}, the answer offers ${exp}`);
    else if (!same(r.dir, exp)) push("peerWrong", `${id} peer ${p} loads ${manifest(r.dir).version}, the answer offers ${exp}`);
    else out.ok++;
  }
  for (const [key, cid] of Object.entries(n.rows)) {
    out.edges++;
    const r = locate(dir, key);
    if (!r.dir) {
      // a package for another os or cpu, which Berry disables
      if (E[cid].conds) push("disabled", `${id} -> ${key}: ${r.err}`);
      else push("unloaded", `${id} -> ${key}: ${r.err}`);
      continue;
    }
    if (!same(r.dir, cid)) { push("wrong", `${id} -> ${key} loads ${manifest(r.dir).version}, the answer ${cid}`); continue; }
    out.ok++;
    const c = E[cid];
    const ctx2 = {};
    for (const p of Object.keys(c.peers)) {
      if (n.rows[p] !== undefined) ctx2[p] = n.rows[p];
      else if (id !== "" && n.peers[p] !== undefined) ctx2[p] = ctx[p] === undefined ? null : ctx[p];
      else if (n.name === p) ctx2[p] = id;
      else ctx2[p] = null;
    }
    queue.push({ dir: r.dir, id: cid, ctx: ctx2 });
  }
}
out.counts = cnt;
console.log(JSON.stringify(out, null, 1));
