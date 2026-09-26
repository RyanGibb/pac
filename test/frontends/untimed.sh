# the output less its timing lines, which vary from run to run, and the
# exit status, which a pipe into sed would lose
untimed() { "$@" > out 2>&1; s=$?; sed -E '/^(parse|solve) [0-9.]+s$/d' out; return $s; }
