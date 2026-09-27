bsd-mailx asks for default-mta | mail-transport-agent and for
liblockfile1 (>= 1.0); exim4-daemon-light provides both virtual names,
postfix the second, and each conflicts with mail-transport-agent.

  $ . ../../frontends/untimed.sh

The alternation is <alts default-mta:amd64 (T) | mail-transport-agent:amd64 (T)>,
one version per alternative; each virtual name has a selector, <sel
default-mta:amd64 (T)> and <sel mail-transport-agent:amd64 (T)>, whose
versions ref:exim4-daemon-light:amd64=4.98.2 and ref:postfix:amd64=3.10.11
are its providers.  The edge into the alternation is one hyperedge to both
its versions, and a conflict is the edge into the other provider at {⊥}.
The core is 13 packages and 9 edges, every ⊥ among them.  <sel
mail-transport-agent:amd64 (T)> is reached though the answer holds no
version of it.

  $ untimed ../../../bin/main.exe debian --core Packages bsd-mailx
  core: 13 packages, 9 edges
  <alts default-mta:amd64 (T) | mail-transport-agent:amd64 (T)> alt:default-mta:amd64 (T)
    -> <sel default-mta:amd64 (T)> {ref:exim4-daemon-light:amd64=4.98.2}
  <alts default-mta:amd64 (T) | mail-transport-agent:amd64 (T)> alt:mail-transport-agent:amd64 (T)
    -> <sel mail-transport-agent:amd64 (T)> {ref:exim4-daemon-light:amd64=4.98.2, ref:postfix:amd64=3.10.11}
  <sel default-mta:amd64 (T)> ref:exim4-daemon-light:amd64=4.98.2
    -> exim4-daemon-light:amd64 {4.98.2}
  <sel mail-transport-agent:amd64 (T)> ref:exim4-daemon-light:amd64=4.98.2
    -> exim4-daemon-light:amd64 {4.98.2}
  <sel mail-transport-agent:amd64 (T)> ref:postfix:amd64=3.10.11
    -> postfix:amd64 {3.10.11}
  bsd-mailx:amd64 8.1.2
    -> <alts default-mta:amd64 (T) | mail-transport-agent:amd64 (T)> {alt:default-mta:amd64 (T), alt:mail-transport-agent:amd64 (T)}
    -> liblockfile1:amd64 {1.17}
  bsd-mailx:amd64 ⊥
  exim4-daemon-light:amd64 4.98.2
    -> postfix:amd64 {⊥}
  exim4-daemon-light:amd64 ⊥
  liblockfile1:amd64 1.17
  liblockfile1:amd64 ⊥
  postfix:amd64 3.10.11
    -> exim4-daemon-light:amd64 {⊥}
  postfix:amd64 ⊥
  packages (3):
    bsd-mailx:amd64 8.1.2
    exim4-daemon-light:amd64 4.98.2
    liblockfile1:amd64 1.17
  encoded solution: 6 core nodes (9 lookups)
  loaded: 4 names, 4 versions

Asked for postfix as well, postfix's conflict edge leaves <sel
default-mta:amd64 (T)> no provider, so the alternation takes
mail-transport-agent and its selector takes postfix:

  $ untimed ../../../bin/main.exe debian Packages bsd-mailx postfix
  packages (3):
    bsd-mailx:amd64 8.1.2
    liblockfile1:amd64 1.17
    postfix:amd64 3.10.11
  encoded solution: 6 core nodes (10 lookups)
  loaded: 4 names, 4 versions
