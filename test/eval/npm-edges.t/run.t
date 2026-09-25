A peer can be installed only because another peer was: chain-app depends
on relay, relay peers on hub, and hub peers on base.  chain-app.lock is
what npm 11.17.0 wrote for chain-app, and pac places all three beside
chain-app too, so the two answers are the same resolution.  pac hands each
declarer's peer to the package that selected the declarer, and chain-app
selected hub, through relay's peer, so base's edge leaves chain-app as
well.

  $ ../../../src/main.exe npm --offline --cache . --tree ./chain-app/package.json | sed -E '/^(parse|solve) [0-9.]+s$/d' > ours
  $ cat ours
  root chain-app 1.0.0
  packages (4):
    base 1.0.0
    chain-app 1.0.0
    hub 1.0.0
    relay 1.0.0
  node_modules (3 edges):
    chain-app 1.0.0 <- base 1.0.0
    chain-app 1.0.0 <- hub 1.0.0
    chain-app 1.0.0 <- relay 1.0.0
  cone: 4 packages, 4 versions, 0 packuments fetched
  encoded solution: 7 core nodes (14 lookups)

Raw, npm's lockfile has each peer edge leave its declarer.

  $ python3 ../../../eval/npm/edges.py chain-app chain-app.lock ours raw | sed 's/  */ /g'
  chain-app nodes ours=4 npm=4 agree=4 ours-only=0 npm-only=0 | edges ours=3 npm=3 agree=1 ours-only=2 npm-only=2 #4,4,4,3,3,1
  $ cat raw.edges.npmonly
  hub	1.0.0	base	base	1.0.0
  relay	1.0.0	hub	hub	1.0.0

--peer-parent moves each to whoever selected the declarer, and hub was
selected by the peer edge moved before it, not by a dependency.

  $ python3 ../../../eval/npm/edges.py chain-app chain-app.lock ours norm --peer-parent | sed 's/  */ /g'
  chain-app nodes ours=4 npm=4 agree=4 ours-only=0 npm-only=0 | edges ours=3 npm=3 agree=3 ours-only=0 npm-only=0 #4,4,4,3,3,3
