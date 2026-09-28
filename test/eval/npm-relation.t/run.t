host's optional peer on nat is the dist-tag latest, which the answer
leaves open, and the lookup from host finds the root's nat 0.1.11 anyway.
npm fetches a tag as the version the packument's dist-tags give it, and
latest is 0.1.11, so the tree holds the answer.

  $ python3 ../../../eval/npm/relation.py latest/package-lock.json tree cache; echo $?
  0

Without the snapshot the tag is read as a range, which nothing satisfies.

  $ python3 ../../../eval/npm/relation.py latest/package-lock.json tree; echo $?
  host 1.0.0 at node_modules/host peers on nat, which the answer leaves open, yet it finds nat 0.1.11 outside latest
  3

next is 0.2.0, which the copy found is not.

  $ python3 ../../../eval/npm/relation.py next/package-lock.json tree cache; echo $?
  host 1.0.0 at node_modules/host peers on nat, which the answer leaves open, yet it finds nat 0.1.11 outside next (0.2.0)
  3
