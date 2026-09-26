#!/usr/bin/env node
// For each {key, spec, version} of the JSON array on stdin, whether the
// version meets the spec as arborist's dep-valid.js reads a registry
// range, loosely: null where npm-package-arg reads the spec as no range or
// version, an alias's target included, and otherwise true or false, false
// for a null version.  reach.py asks it, so that ranges are read with
// npm's own npm-package-arg and semver.
// usage: ranges.js < asks.json
'use strict'
const fs = require('fs')
const lib = require('./npmlib')
const npa = lib('npm-package-arg')
const semver = lib('semver')

const asks = JSON.parse(fs.readFileSync(0, 'utf8'))
console.log(JSON.stringify(asks.map(({ key, spec, version }) => {
  let range
  try {
    const a = npa.resolve(key, spec)
    const r = a.type === 'alias' ? a.subSpec : a
    if (r.type !== 'range' && r.type !== 'version') return null
    range = r.fetchSpec
  } catch (e) {
    return null
  }
  return version !== null && semver.satisfies(version, range, true)
})))
