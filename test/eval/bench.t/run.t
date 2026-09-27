stratify.py draws a benchmark set from a finished run: of the queries both
sides answered in the tool's order, less the regression set (bash is
Alpine's), K from each tenth by the size of pac's answer, seeded.

  $ mkdir -p run/out
  $ for i in $(seq 1 30); do
  >   echo "p$i" >> run/queries.txt
  >   echo "query=p$i mode=tool pac=ok tool=ok wall=1" >> run/results.txt
  >   echo "query=p$i mode=pubgrub pac=ok tool=ok wall=1" >> run/results.txt
  >   printf 'packages (%d):\n' $((i * 3)) > run/out/p$i.tool.out
  > done
  $ echo bash >> run/queries.txt
  $ echo "query=bash mode=tool pac=ok tool=ok wall=1" >> run/results.txt
  $ printf 'packages (1):\n' > run/out/bash.tool.out
  $ echo "query=q mode=tool pac=unsat tool=ok wall=1" >> run/results.txt
  $ python3 ../../../eval/bench/stratify.py alpine run 7 1 | tee s1
  stratum0	p2
  stratum1	p4
  stratum2	p8
  stratum3	p12
  stratum4	p13
  stratum5	p16
  stratum6	p21
  stratum7	p22
  stratum8	p26
  stratum9	p30
  $ python3 ../../../eval/bench/stratify.py alpine run 7 1 | cmp - s1
  $ python3 ../../../eval/bench/stratify.py alpine run 8 2 | wc -l
  20

summary.py reads bench.sh's rows: per query and variant the median of
the measured runs, the warm-up left out, and pac's time over the tool's.

  $ mkdir -p b/res/alpine/regress
  $ cat > b/res/alpine/regress/x.csv <<'EOF'
  > alpine,regress,"x",pac-tool,0,9.0,0.01,0.02,1000,0,t,0.1
  > alpine,regress,"x",pac-pubgrub,0,9.0,0.01,0.03,1000,0,t,0.1
  > alpine,regress,"x",apk,0,9.0,,,2048,0,t,0.1
  > alpine,regress,"x",pac-tool,1,0.10,0.01,0.02,1024,0,t,0.1
  > alpine,regress,"x",pac-pubgrub,1,0.20,0.01,0.03,1024,0,t,0.1
  > alpine,regress,"x",apk,1,0.40,,,2048,0,t,0.1
  > alpine,regress,"x",pac-tool,2,0.30,0.01,0.02,1024,0,t,0.1
  > alpine,regress,"x",pac-pubgrub,2,0.20,0.01,0.03,1024,0,t,0.1
  > alpine,regress,"x",apk,2,0.20,,,2048,1,t,0.1
  > EOF

Two more queries, measured once each, so that the geometric mean of the
ratios has an interval: the queries resampled, seeded, so it is the same
on every run.

  $ cat > b/res/alpine/regress/y.csv <<'EOF'
  > alpine,regress,"y",pac-tool,1,0.10,0.01,0.02,1024,0,t,0.1
  > alpine,regress,"y",pac-pubgrub,1,0.40,0.01,0.03,1024,0,t,0.1
  > alpine,regress,"y",apk,1,0.20,,,2048,0,t,0.1
  > EOF
  $ cat > b/res/alpine/regress/z.csv <<'EOF'
  > alpine,regress,"z",pac-tool,1,0.90,0.01,0.02,1024,0,t,0.1
  > alpine,regress,"z",pac-pubgrub,1,0.30,0.01,0.03,1024,0,t,0.1
  > alpine,regress,"z",apk,1,0.30,,,2048,0,t,0.1
  > EOF
  $ python3 ../../../eval/bench/summary.py b
  
  ## alpine, regress
  
  | query | pac-tool parse / solve | pac-tool wall (IQR) | pac-tool MiB | pac-pubgrub parse / solve | pac-pubgrub wall (IQR) | pac-pubgrub MiB | apk wall (IQR) | apk MiB | pac-tool ÷ apk | pac-pubgrub ÷ apk |
  |---|---|---|---|---|---|---|---|---|---|---|
  | x | 0.01 / 0.02 | 0.200 (0.100) | 1 | 0.01 / 0.03 | 0.200 (0.000) | 1 | 0.300 (0.100) | 2 | 0.67 | 0.67 |
  | y | 0.01 / 0.02 | 0.100 (0.000) | 1 | 0.01 / 0.03 | 0.400 (0.000) | 1 | 0.200 (0.000) | 2 | 0.50 | 2.00 |
  | z | 0.01 / 0.02 | 0.900 (0.000) | 1 | 0.01 / 0.03 | 0.300 (0.000) | 1 | 0.300 (0.000) | 2 | 3.00 | 1.00 |
  | **median over queries** |  | 0.200 |  |  | 0.300 |  | 0.300 |  | gm 1.00× (95% CI 0.50–3.00) | gm 1.10× (95% CI 0.67–2.00) |
  | **sum of medians** |  | 1.2 |  |  | 0.9 |  | 0.8 |  | pac faster on 2/3 | pac faster on 1/3 |
  
  - x apk exit 0,1
  
  rows ending at load >= 3.5: 0 of 15
  $ head -2 b/bench.csv
  step,set,query,variant,rep,wall_s,parse_s,solve_s,maxrss_kb,rc,end_utc,load1,ratio_gm,ci_lo,ci_hi
  alpine,regress,x,pac-tool,0,9.0,0.01,0.02,1000,0,t,0.1,,,
  $ grep ',gm,' b/bench.csv
  alpine,regress,*,pac-tool,gm,,,,,,,,1.000000,0.500000,3.000000
  alpine,regress,*,pac-pubgrub,gm,,,,,,,,1.100642,0.666667,2.000000
  $ python3 ../../../eval/bench/summary.py b c.csv > /dev/null
  $ cmp b/bench.csv c.csv
