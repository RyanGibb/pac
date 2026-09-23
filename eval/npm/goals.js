#!/usr/bin/env node
// Goals for scale.sh, as name@spec, from every packument in a snapshot.
// By default spec is the version a bare `npm install <name>` installs, which
// npm-package-arg reads as the range "*": npm's own npm-pick-manifest asked
// for "*" at the host npm-version records.  A packument with no such version
// is left out.  With `targeted`, spec is a range, one pool per line prefix,
// for the root edges a pinned goal never exercises:
//   star-deprecated   "*" where dist-tags.latest is deprecated
//   star-engines      "*" where dist-tags.latest fails the host's engines
//   star-prerelease   "*" where dist-tags.latest is a prerelease, which
//                     npm-pick-manifest takes for "*" and for no other range
//   major-deprecated  "M.x" where M's newest release is deprecated and an
//                     older release in M is not
//   major-engines     "M.x" where M's newest release fails the host's engines
//                     and an older release in M passes
// usage: goals.js <snapshot-dir> [targeted]
'use strict'
const fs = require('fs')
const path = require('path')
// npm's own copies, beside the npm on PATH, so the picks are that npm's
const npm = require('child_process').execSync('command -v npm').toString().trim()
const lib = m => require(path.join(path.dirname(path.dirname(fs.realpathSync(npm))), 'node_modules', m))
const pick = lib('npm-pick-manifest')
const semver = lib('semver')
const { checkEngine } = lib('npm-install-checks')

const [dir, mode] = process.argv.slice(2)
const [npmVersion, nodeVersion] =
  fs.readFileSync(path.join(__dirname, 'npm-version'), 'utf8').trim().split('\n')
const engineOk = m => {
  try { checkEngine(m, npmVersion, nodeVersion); return true } catch (e) { return false }
}

for (const f of fs.readdirSync(dir).filter(f => f.endsWith('.json')).sort()) {
  const name = f.slice(0, -5).replace(/%2F/g, '/')
  let pk
  try { pk = JSON.parse(fs.readFileSync(path.join(dir, f), 'utf8')) } catch (e) { continue }
  if (mode !== 'targeted') {
    try { console.log(`${name}@${pick(pk, '*', { nodeVersion, npmVersion }).version}`) } catch (e) {}
    continue
  }
  const vs = pk.versions || {}
  const lat = (pk['dist-tags'] || {}).latest
  const out = (pool, range) => console.log(`${pool}\t${name}@${range}`)
  if (vs[lat]) {
    if (vs[lat].deprecated) out('star-deprecated', '*')
    else if (!engineOk(vs[lat])) out('star-engines', '*')
    else if (semver.prerelease(lat, { loose: true })) out('star-prerelease', '*')
  }
  const byMajor = new Map()
  for (const [v, m] of Object.entries(vs)) {
    const p = semver.parse(v, { loose: true })
    if (p && !p.prerelease.length) byMajor.set(p.major, [...(byMajor.get(p.major) || []), [v, m]])
  }
  for (const [major, list] of byMajor) {
    list.sort((a, b) => semver.rcompare(a[0], b[0], { loose: true }))
    const top = list[0][1]
    if (top.deprecated && list.some(([, m]) => !m.deprecated)) out('major-deprecated', `${major}.x`)
    if (!engineOk(top) && list.some(([, m]) => engineOk(m))) out('major-engines', `${major}.x`)
  }
}
