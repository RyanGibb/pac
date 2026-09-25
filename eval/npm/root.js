#!/usr/bin/env node
// The package.json npm resolves for `npm install <query>` in an empty
// project, written with npm's own npm-package-arg and arborist's
// addRmPkgDeps.add, so npm's question is posed without pac's reading of
// the query.  This is the manifest before npm saves its picks over the
// specs: `npm ci` checks an answer against it.  A tag becomes the version
// the snapshot's packument tags, as arborist's #add makes it, and is added
// after the rest, as #add's await orders it.
// usage: root.js <snapshot-dir> <spec>...
'use strict'
const fs = require('fs')
const path = require('path')
const npm = require('child_process').execSync('command -v npm').toString().trim()
const lib = m => require(path.join(path.dirname(path.dirname(fs.realpathSync(npm))), 'node_modules', m))
const npa = lib('npm-package-arg')
const { add } = lib('@npmcli/arborist/lib/add-rm-pkg-deps.js')

const [dir, ...query] = process.argv.slice(2)
const specs = query.map(a => npa(a))
const plain = specs.filter(s => !(s.rawSpec && s.type === 'tag'))
const tagged = specs.filter(s => s.rawSpec && s.type === 'tag').map(s => {
  const pk = JSON.parse(fs.readFileSync(path.join(dir, s.name.replace(/\//g, '%2F') + '.json'), 'utf8'))
  const v = (pk['dist-tags'] || {})[s.fetchSpec]
  if (!v) throw new Error(`${s.raw}: no such dist-tag`)
  return npa(`${s.name}@${v}`)
})
console.log(JSON.stringify(add({ pkg: {}, add: [...plain, ...tagged] }), null, 2))
