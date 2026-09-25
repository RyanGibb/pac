#!/usr/bin/env node
// Each package of a package-lock.json that nothing reaches from the root,
// as "unreached <path>": the entries `npm install --package-lock-only`
// prunes because nothing needs them, not because anything is wrong with
// them.  npm judges none of their own dependencies either, so each one a
// registry range names that lookup does not meet is "unmet <path> <key>
// <spec>".
//
// An edge is followed where node_modules lookup takes it from its
// requirer, a peer's included: npm resolves a peer from its declarer too,
// and a copy the declarer holds in its own node_modules is PEER LOCAL, an
// invalid edge (arborist edge.js), so such a copy counts as reached and
// its removal as a repair.  Ranges are read with npm's own npm-package-arg
// and semver, loosely, as arborist's dep-valid.js reads them.
// usage: reach.js <package-lock.json>
'use strict'
const fs = require('fs')
const path = require('path')
const npm = require('child_process').execSync('command -v npm').toString().trim()
const lib = m => require(path.join(path.dirname(path.dirname(fs.realpathSync(npm))), 'node_modules', m))
const npa = lib('npm-package-arg')
const semver = lib('semver')

const pk = JSON.parse(fs.readFileSync(process.argv[2], 'utf8')).packages

// "" then each package directory on the way down to p, as lockname.py's
function ancestors (p) {
  const out = ['']
  const segs = p ? p.split('/') : []
  for (let i = 0; i < segs.length;) {
    const take = i + 1 < segs.length && segs[i + 1].startsWith('@') ? 3 : 2
    out.push(segs.slice(0, i + take).join('/'))
    i += take
  }
  return out
}

function resolve (from, key) {
  for (const a of ancestors(from).reverse()) {
    const slot = (a ? a + '/node_modules/' : 'node_modules/') + key
    if (slot in pk) return slot
  }
  return null
}

function edges (p) {
  const e = pk[p]
  const fields = ['dependencies', 'optionalDependencies', 'peerDependencies']
  if (p === '') fields.push('devDependencies')
  const meta = e.peerDependenciesMeta || {}
  const out = []
  for (const f of fields) {
    for (const [key, spec] of Object.entries(e[f] || {})) {
      const optional = f === 'optionalDependencies' || (f === 'peerDependencies' && (meta[key] || {}).optional)
      out.push({ key, spec, optional })
    }
  }
  return out
}

const seen = new Set([''])
const todo = ['']
while (todo.length) {
  const p = todo.pop()
  for (const { key } of edges(p)) {
    const q = resolve(p, key)
    if (q !== null && !seen.has(q)) { seen.add(q); todo.push(q) }
  }
}

for (const p of Object.keys(pk).sort()) {
  if (seen.has(p)) continue
  console.log('unreached ' + p)
  for (const { key, spec, optional } of edges(p)) {
    let range
    try {
      const a = npa.resolve(key, spec)
      const r = a.type === 'alias' ? a.subSpec : a
      if (r.type !== 'range' && r.type !== 'version') continue
      range = r.fetchSpec
    } catch (e) {
      continue
    }
    const q = resolve(p, key)
    if (q === null ? !optional : !semver.satisfies(pk[q].version, range, true)) {
      console.log('unmet ' + p + ' ' + key + ' ' + spec)
    }
  }
}
