# scale.sh's totals over results.txt, with -v modes="$MODES".  closed and
# npm's wall time belong to the query, repeated on each of its modes'
# lines, so each counts once; nodes, edges and pac's wall time belong to
# the mode.
{
  delete f
  for (i = 1; i <= NF; i++) {j = index($i, "="); f[substr($i, 1, j - 1)] = substr($i, j + 1)}
  q = f["query"]; qs[q]
  if (f["closed"] == "yes") cl[q]
  if (f["nodes"] != "-") {g++; split(f["nodes"] "," f["edges"], a, ","); for (i = 1; i <= 6; i++) t[i] += a[i]}
  if (f["twall"] != "-") {tw[q] = f["twall"]; pw[f["mode"]] += f["wall"]}
}
END {
  printf "closed %d/%d; over the %d runs both answer, nodes ours=%d npm=%d agree=%d, edges ours=%d npm=%d agree=%d\n",
    length(cl), length(qs), g, t[1], t[2], t[3], t[4], t[5], t[6]
  if (length(tw)) {
    for (q in tw) nw += tw[q]
    printf "wall time over the %d queries npm was asked: npm %.1fs", length(tw), nw
    k = split(modes, ms, " ")
    for (i = 1; i <= k; i++) printf ", pac %s %.1fs", ms[i], pw[ms[i]]
    print ""
  }
}
