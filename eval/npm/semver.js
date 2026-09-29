#!/usr/bin/env node
// For each [version, range, mode] line on stdin, whether npm's own semver
// takes the version, a line of true, false or null where semver throws.
// mode is strict, satisfies itself; loose, as arborist's dep-valid.js asks
// it; or berry, Berry's satisfiesWithPrereleases
// (yarnpkg-core/sources/semverUtils.ts): the range with includePrerelease,
// and else the version and every comparator with their prerelease tags
// dropped.  tree.py's satisfies asks it.
'use strict'
const semver = require('./npmlib')('semver')

function berry (version, range) {
  let r, v
  try { r = new semver.Range(range, { includePrerelease: true }) } catch (e) { return false }
  try { v = new semver.SemVer(version, r) } catch (e) { return false }
  if (r.test(v)) return true
  if (v.prerelease) v.prerelease = []
  return r.set.some(set => {
    for (const c of set) if (c.semver.prerelease) c.semver.prerelease = []
    return set.every(c => c.test(v))
  })
}

const sat = {
  strict: (v, r) => semver.satisfies(v, r),
  loose: (v, r) => semver.satisfies(v, r, true),
  berry
}

require('readline').createInterface({ input: process.stdin }).on('line', l => {
  const [v, r, mode] = JSON.parse(l)
  let ok
  try { ok = sat[mode](v, r) } catch (e) { ok = null }
  process.stdout.write(JSON.stringify(ok) + '\n')
})
