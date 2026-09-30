cargo's index rows, with CARGO_INDEX a relative path.

  $ mkdir -p idx/se/rd
  $ echo '{"name":"serde","vers":"1.0.0","deps":[],"cksum":"ab","features":{},"yanked":false}' > idx/se/rd/serde
  $ export CARGO_INDEX=idx PYTHONPATH=../../../eval/cargo
  $ python3 -c 'import run_query as r; print(r.index_line("serde", "1.0.0")["cksum"], r.newest("serde")["vers"])'
  ab 1.0.0
  $ python3 -c 'import scale; print(scale.summary("se/rd/serde")["vers"])'
  [('1.0.0', None)]
