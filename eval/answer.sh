# Sourced wherever pac's output is read: every frontend prints its answer
# as a "packages (N):" line and N rows under it, each indented two spaces.

rows() {  # <pac output>: the answer's rows, unindented
  awk '/^packages \(/ {s = 1; next} s && /^  / {print substr($0, 3); next} s {exit}' "$1"
}

# whether the block holds every row its header counts: a line that is no
# row ends the block early, and the rows after it would go unjudged
whole() {  # <pac output>
  [ "$(sed -n 's/^packages (\([0-9]*\)):$/\1/p' "$1")" = "$(rows "$1" | wc -l)" ]
}
