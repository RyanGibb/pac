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
  $ python3 ../../../eval/bench/summary.py b

  ## alpine, regress

  | query | pac-tool parse / solve | pac-tool wall (IQR) | pac-tool MiB | pac-pubgrub parse / solve | pac-pubgrub wall (IQR) | pac-pubgrub MiB | apk wall (IQR) | apk MiB | pac-tool ÷ apk | pac-pubgrub ÷ apk |
  |---|---|---|---|---|---|---|---|---|---|---|
  | x | 0.01 / 0.02 | 0.200 (0.100) | 1 | 0.01 / 0.03 | 0.200 (0.000) | 1 | 0.300 (0.100) | 2 | 0.67 | 0.67 |
  | **median over queries** |  | 0.200 |  |  | 0.200 |  | 0.300 |  | gm 0.67 | gm 0.67 |
  | **sum of medians** |  | 0.2 |  |  | 0.2 |  | 0.3 |  | pac faster on 1/1 | pac faster on 1/1 |

  - x apk exit 0,1

  rows ending at load >= 3.5: 0 of 9
  $ head -2 b/bench.csv
  step,set,query,variant,rep,wall_s,parse_s,solve_s,maxrss_kb,rc,end_utc,load1
  alpine,regress,x,pac-tool,0,9.0,0.01,0.02,1000,0,t,0.1
