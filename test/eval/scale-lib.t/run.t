The harness around a toy ecosystem (toy.sh).  A queries file may name one
query in two pools; the query is still asked once.

  $ export EVAL=$(cd ../../../eval && pwd) P=2 MODES=tool
  $ touch pac
  $ printf 'p1\ta\np2\ta\nb\n' > q
  $ bash toy.sh pac run q
  toy.sh: 2 of 2 queries to run
  tool: 2 queries, exact 2/2, valid 2/2, minimal 2/2
  $ sort run/asked
  a
  b

The queries file is read once, so a pipe will do.

  $ bash -c 'bash toy.sh pac run2 <(printf "a\nb\n")'
  toy.sh: 2 of 2 queries to run
  tool: 2 queries, exact 2/2, valid 2/2, minimal 2/2

A comparison that fails is no correspondence either way, and the summary
counts it apart, as it does every run pac gave no answer on.

  $ printf 'a\nbroken\nu\n' > q3
  $ bash toy.sh pac run3 q3
  toy.sh: 3 of 3 queries to run
  tool: 3 queries, exact 1/2, valid 2/2, minimal 2/2, uncompared 1, pac unsat 1
  $ sed 's/ wall=[^ ]*//' run3/results.txt
  query=a mode=tool pac=ok tool=ok corr=exact valid=VALID minimal=yes reproduced=- oo=0 to=0 pin=- parse=0.10 solve=0.01 core=3 lookups=5 names=7 versions=9 answer=f0377fa310a375fc
  query=broken mode=tool pac=ok tool=ok corr=ERR valid=VALID minimal=yes reproduced=- oo=- to=- pin=- parse=0.10 solve=0.01 core=3 lookups=5 names=7 versions=9 answer=fafe3da42b52c6c4
  query=u mode=tool pac=unsat tool=ok corr=- valid=- minimal=- reproduced=- oo=- to=- pin=- parse=0.10 solve=0.01 core=- lookups=- names=7 versions=9 answer=-

Each line carries pac's own counts and times, and a hash of its answer
without them: seeds 0 and 2 answer "a" alike, in different times, and
seed 1 otherwise.  A fuzz run counts the distinct answers.

  $ printf 'a\nb\nu\n' > q4
  $ FUZZ=3 MODES= bash toy.sh pac run4 q4
  toy.sh: 3 of 3 queries to run
  fuzz: 3 queries x 3 seeds = 9 runs; pac ok 6, unsat 3, refuse 0, io-error 0, timeout 0, crash 0
  fuzz: valid 6, INVALID 0 (in 0 queries), ERR 0, cyclic 0; minimal 6/6
  fuzz: 3 distinct answers over the 2 queries answered; 1 answered more than one way, at most 2
  fuzz: 0 queries answered under some seeds and unsat under others (split.txt)
  $ sed 's/ tool=.* pin=-//' run4/results.txt
  query=a mode=random-0 pac=ok parse=0.10 solve=0.01 core=3 lookups=5 names=7 versions=9 answer=f0377fa310a375fc
  query=a mode=random-1 pac=ok parse=0.10 solve=0.01 core=3 lookups=5 names=7 versions=9 answer=b6b8ce7060c8ba42
  query=a mode=random-2 pac=ok parse=0.10 solve=0.02 core=3 lookups=5 names=7 versions=9 answer=f0377fa310a375fc
  query=b mode=random-0 pac=ok parse=0.10 solve=0.01 core=3 lookups=5 names=7 versions=9 answer=c81128b511b73db0
  query=b mode=random-1 pac=ok parse=0.10 solve=0.01 core=3 lookups=5 names=7 versions=9 answer=c81128b511b73db0
  query=b mode=random-2 pac=ok parse=0.10 solve=0.02 core=3 lookups=5 names=7 versions=9 answer=c81128b511b73db0
  query=u mode=random-0 pac=unsat parse=0.10 solve=0.01 core=- lookups=- names=7 versions=9 answer=-
  query=u mode=random-1 pac=unsat parse=0.10 solve=0.01 core=- lookups=- names=7 versions=9 answer=-
  query=u mode=random-2 pac=unsat parse=0.10 solve=0.02 core=- lookups=- names=7 versions=9 answer=-
