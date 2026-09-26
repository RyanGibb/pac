The paper's Debian worked example: bsd-mailx asks for default-mta |
mail-transport-agent and for liblockfile1 (>= 1.0); exim4-daemon-light
provides both virtual names, postfix the second, and each conflicts with
mail-transport-agent.  Packages is the figure's index with the
Architecture field its cut drops.

  $ . ../../frontends/untimed.sh

In the figure's notation, pac's names read:
- <alts default-mta:amd64 (T) | mail-transport-agent:amd64 (T)> is <A_1>,
and its versions alt:default-mta:amd64 (T) and
alt:mail-transport-agent:amd64 (T) are the alternatives <a_1> and <a_2>;
- <sel default-mta:amd64 (T)> is the selector <a_1>, and
<sel mail-transport-agent:amd64 (T)> is <a_2>;
- ref:exim4-daemon-light:amd64=4.98.2 is <exim4-daemon-light, 4.98.2>, and
ref:postfix:amd64=3.10.11 is <postfix, 3.10.11>;
- a real name n:amd64 is n.
All 13 packages and 9 edges of the figure's reduction are here and nothing
else: the edge into <A_1> is one hyperedge to both its versions, and a
conflict is the edge into the other provider at {⊥}.  The figure draws
every ⊥, so none is omitted.  <a_2> is reached though the answer holds no
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

Asked for postfix as well, postfix's conflict edge leaves <a_1> no
provider, so <A_1> takes <a_2> and <a_2> takes postfix, as the example
says:

  $ untimed ../../../bin/main.exe debian Packages bsd-mailx postfix
  packages (3):
    bsd-mailx:amd64 8.1.2
    liblockfile1:amd64 1.17
    postfix:amd64 3.10.11
  encoded solution: 6 core nodes (10 lookups)
  loaded: 4 names, 4 versions
