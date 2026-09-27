# the output less its timing lines, which vary from run to run, and the
# exit status, which a pipe into sed would lose
untimed() { "$@" > out 2>&1; s=$?; sed -E '/^(parse|solve) [0-9.]+s$/d' out; return $s; }

# the part of that output a case asks about, the exit status kept: the
# lines from one starting $1 to one starting $2, the first $1 lines, or
# the lines holding $1
between() { a=$1 b=$2; shift 2; untimed "$@" > part; s=$?; sed -n "/^$a/,/^$b/p" part; return $s; }
first() { n=$1; shift; untimed "$@" > part; s=$?; head -n "$n" part; return $s; }
holding() { h=$1; shift; untimed "$@" > part; s=$?; grep -- "$h" part; return $s; }
