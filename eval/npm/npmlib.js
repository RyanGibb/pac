// npm's own copy of a module, beside the npm on PATH, so that what a script
// reads with it is that npm's reading
'use strict'
const fs = require('fs')
const path = require('path')
const npm = require('child_process').execSync('command -v npm').toString().trim()
module.exports = m => require(path.join(path.dirname(path.dirname(fs.realpathSync(npm))), 'node_modules', m))
