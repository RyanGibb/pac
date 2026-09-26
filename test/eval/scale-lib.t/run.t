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
  query=a mode=tool pac=ok tool=ok corr=exact valid=VALID minimal=yes oo=0 to=0 pin=-
  query=broken mode=tool pac=ok tool=ok corr=ERR valid=VALID minimal=yes oo=- to=- pin=-
  query=u mode=tool pac=unsat tool=ok corr=- valid=- minimal=- oo=- to=- pin=-
