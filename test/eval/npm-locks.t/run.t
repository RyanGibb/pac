layout-check.sh judges a lock by resolve.js and lockname.py, which must
take npm's own locks.  dev is what npm 11.17.0 locks for a project whose
b is ^1 in dependencies and ^2 in devDependencies: arborist loads a
root's devDependencies last, so ^2 wins and b is 2.0.0.

  $ node ../../../eval/npm/resolve.js dev/package-lock.json dev/package.json "$PWD/skel"; echo $?
  0

key is what it locks for a project whose p depends on x as an alias of b
^2, and whose root overrides x to 1.0.0: the override replaces the
aliased spec, and x is the registry's own x.

  $ node ../../../eval/npm/resolve.js key/package-lock.json key/package.json "$PWD/skel"; echo $?
  0
  $ python3 ../../../eval/npm/lockname.py key/package-lock.json key/package.json; echo $?
  0
