#!/usr/bin/env node
// Every edge of a package-lock.json resolved as node itself resolves it:
// the lock's tree is laid out on disk as bare directories, each holding a
// package.json with the entry's name and version, and each edge is
// require.resolve'd from its depender's directory.  An edge holds when it
// lands on the package its spec names (the alias's target for npm:, the key
// otherwise) at a version the spec admits, as npm's dep-valid reads it
// (semver.satisfies, loose; a tag or * admits any version), under the root's
// flat override on the key.  A peer landing in the declarer's own
// node_modules is PEER LOCAL, below the root.  A missing optional
// dependency or optional peer holds; another missing edge does not.  Specs
// off the registry (git, file, url) are not judged.
// usage: resolve.js <package-lock.json> <root package.json> <scratch-dir>
// Prints one line per miss and exits 3 if there is any.
'use strict'
const fs = require('fs')
const path = require('path')
const lib = require('./npmlib')
const semver = lib('semver')
const npa = lib('npm-package-arg')

const [lockp, rootp, dir] = process.argv.slice(2)
const pk = JSON.parse(fs.readFileSync(lockp, 'utf8')).packages
const root = JSON.parse(fs.readFileSync(rootp, 'utf8'))
const ovr = {}
for (const [k, v] of Object.entries(root.overrides || {})) {
  if (typeof v === 'string' && v !== '*' && v !== '') ovr[k] = v
}

fs.rmSync(dir, { recursive: true, force: true })
const at = p => path.join(dir, 'root', p)
fs.mkdirSync(at(''), { recursive: true })
fs.writeFileSync(path.join(at(''), 'package.json'), JSON.stringify({ name: 'root', version: '1.0.0' }))
for (const [p, e] of Object.entries(pk)) {
  if (!p || e.link) continue
  fs.mkdirSync(at(p), { recursive: true })
  const name = e.name || p.slice(p.lastIndexOf('node_modules/') + 13)
  fs.writeFileSync(path.join(at(p), 'package.json'), JSON.stringify({ name, version: e.version }))
}

let bad = 0
const miss = (p, why) => { console.log(`${p || '(root)'} ${why}`); bad = 3 }
for (const [p, e] of Object.entries(pk)) {
  if (e.link) continue
  const top = p === ''
  const m = top ? root : e
  // arborist loads a root's devDependencies last, so they win
  const dev = top ? (m.devDependencies || {}) : {}
  const deps = { ...(m.dependencies || {}), ...(m.optionalDependencies || {}), ...dev }
  const optional = new Set(Object.keys(m.optionalDependencies || {}).filter(k => !(k in dev)))
  const meta = m.peerDependenciesMeta || {}
  const edges = Object.entries(deps).map(([k, s]) => [k, s, 'dep', optional.has(k)])
  for (const [k, s] of Object.entries(m.peerDependencies || {})) {
    if (!(k in deps)) edges.push([k, s, 'peer', !!(meta[k] && meta[k].optional)])
  }
  for (const [k, raw, kind, opt] of edges) {
    let spec
    try { spec = npa.resolve(k, k in ovr ? ovr[k] : raw) } catch (err) { continue }
    let want = k
    if (spec.type === 'alias') { want = spec.subSpec.name; spec = spec.subSpec }
    if (!['range', 'version', 'tag'].includes(spec.type)) continue
    let found
    try { found = require.resolve(`${k}/package.json`, { paths: [at(p)] }) } catch (err) { found = null }
    if (!found || !found.startsWith(at('') + path.sep)) {
      if (!opt) miss(p, `${kind} ${k}@${raw}: missing`)
      continue
    }
    const q = path.relative(at(''), path.dirname(found))
    if (kind === 'peer' && !top && q === (p ? p + '/' : '') + 'node_modules/' + k) {
      miss(p, `${kind} ${k}@${raw}: PEER LOCAL at ${q}`)
      continue
    }
    const got = JSON.parse(fs.readFileSync(found, 'utf8'))
    if (got.name !== want) { miss(p, `${kind} ${k}@${raw}: ${q} is ${got.name}`); continue }
    if (spec.type !== 'tag' && spec.fetchSpec !== '*' &&
        !semver.satisfies(got.version, spec.fetchSpec, true)) {
      miss(p, `${kind} ${k}@${raw}: ${q} is ${got.version}`)
    }
  }
}
fs.rmSync(dir, { recursive: true, force: true })
process.exit(bad)
