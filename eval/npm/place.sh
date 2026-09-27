# Sourced by scale.sh under READING=placement, whose answer is a
# node_modules layout rather than a resolution relation: pac's layout is
# written out as a lock by lockgen.py, judged by layout-check.sh, and
# scored against npm's own lock by layout_cmp.py, both as a layout and as
# the resolution relation edges.py reads off each lock.  The queries,
# snapshot, shim, npm and closure are scale.sh's.  DEPTH is pac's --depth.
export DEPTH=${DEPTH:-8}

params() { echo "READING=$READING"; echo "DEPTH=$DEPTH"; }

run_pac() {
  rm -f "$2.cmp"
  PATH=$run/bin:$PATH PAC_MISS=$o.pacmiss timeout "$TIMEOUT" "$run/pac.exe" npm $(flag "$1") \
    --reading=placement --depth "$DEPTH" --cache "$run/cache" --node-version "$NODEV" \
    --npm-version "$NPMV" $3 > "$2.out" 2>&1
}

correspond() {
  local c
  python3 "$S/lockgen.py" "$run/cache" "$1.out" "$1.lock" "$w/lock/package.json" > /dev/null 2>&1 ||
    return 1
  c=$(cd "$S" && python3 layout_cmp.py "$1.lock" "$o.theirs") || return 1
  echo "$c" > "$1.cmp"
  case $c in layout=exact*) corr=exact ;; *) corr=diff ;; esac
}

# two modes answering the same layout share one check
canon() { grep '^  node_modules/' "$1.out"; }

# the layout is the lock, so there is nothing for npm's relock to settle:
# minimal and reproduced are left -
check() {  # <stem> <query words...>
  local p=$1 v; shift
  mkdir -p "$p.check"
  timeout "$TIMEOUT" bash "$S/layout-check.sh" "$p.out" "$p.check" "$@" > "$p.check/log" 2>&1
  v=" $(tail -n 1 "$p.check/log")"
  valid=$(sed -n 's/.* valid=\([A-Z]*\)$/\1/p' <<< "$v")
  case $valid in VALID|INVALID) ;; *) valid=ERR ;; esac
  minimal=- reproduced=-
}

fields() {
  local c=- why=-
  [ -s "$1.cmp" ] && c=$(tr ' ' ';' < "$1.cmp")
  [ -s "$1.check/log" ] && why=$(tail -n 1 "$1.check/log" | sed 's/ valid=.*//' | tr ' ' ',')
  printf ' twall=%s closed=@closed@ cmp=%s why=%s' "$twall" "$c" "$why"
}

# closure, npm's and pac's wall time, and how many answers are npm's
# layout and relation exactly
totals() {
  awk -v modes="$MODES" '
    {delete f; for (i = 1; i <= NF; i++) {j = index($i, "="); f[substr($i, 1, j - 1)] = substr($i, j + 1)}
     q = f["query"]; qs[q]; m = f["mode"]
     if (f["closed"] == "yes") cl[q]
     if (f["twall"] != "-") {tw[q] = f["twall"]; pw[m] += f["wall"]}
     if (f["cmp"] != "-") {n[m]++; lx[m] += f["cmp"] ~ /^layout=exact/; rx[m] += f["cmp"] ~ /relation=exact/}
     if (f["solve"] != "-") sv[m] += f["solve"]}
    END {printf "closed %d/%d\n", length(cl), length(qs)
      k = split(modes, ms, " ")
      for (i = 1; i <= k; i++) printf "%s: layout-exact %d/%d, relation-exact %d/%d, solve %.2fs\n",
        ms[i], lx[ms[i]], n[ms[i]], rx[ms[i]], n[ms[i]], sv[ms[i]]
      if (length(tw)) {
        for (q in tw) nw += tw[q]
        printf "wall time over the %d queries npm was asked: npm %.1fs", length(tw), nw
        for (i = 1; i <= k; i++) printf ", pac %s %.1fs", ms[i], pw[ms[i]]
        print ""}}' "$run/results.txt"
}
