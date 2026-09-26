npm's totals.  A query's closed and npm's wall time are on each of its
modes' lines, and count once; pac's wall time counts per mode.

  $ cat > results.txt <<'EOF'
  > query=a mode=tool pac=ok tool=ok wall=1.0 twall=10.0 closed=yes nodes=3,3,3 edges=2,2,2
  > query=a mode=pubgrub pac=ok tool=ok wall=2.0 twall=10.0 closed=yes nodes=3,4,3 edges=2,3,2
  > query=b mode=tool pac=ok tool=ok wall=4.0 twall=20.0 closed=no nodes=1,1,1 edges=0,0,0
  > query=b mode=pubgrub pac=unsat tool=ok wall=8.0 twall=20.0 closed=no nodes=- edges=-
  > query=c mode=tool pac=ok tool=- wall=1.0 twall=- closed=yes nodes=- edges=-
  > query=c mode=pubgrub pac=ok tool=- wall=1.0 twall=- closed=yes nodes=- edges=-
  > EOF
  $ awk -v modes="tool pubgrub" -f ../../../eval/npm/totals.awk results.txt
  closed 2/3; over the 3 runs both answer, nodes ours=7 npm=8 agree=7, edges ours=4 npm=5 agree=4
  wall time over the 2 queries npm was asked: npm 30.0s, pac tool 5.0s, pac pubgrub 10.0s
