# The platform opam is asked about: setup.sh pins PLATFORM into the root it
# builds, and pac is handed what that root holds, read back from opam, so
# that a root built earlier, or under another PLATFORM, cannot leave the
# two sides answering for different hosts.  The syntax is pac opam
# --environment's, and as there a variable left out keeps its default, the
# platform the baselines were recorded on, pac's own default.
BASELINE_PLATFORM=os=linux,os-family=debian,os-distribution=debian,os-version=12,arch=x86_64
PLATFORM_VARS="os os-family os-distribution os-version arch"

# spelled out whole, so that opam infers none of them from the host
platform_whole() {  # <bindings>
  local -A pv=()
  local -a bs
  local b v s=
  IFS=, read -ra bs <<< "$BASELINE_PLATFORM${1:+,$1}"
  for b in "${bs[@]}"; do
    case $b in
      os=*|os-family=*|os-distribution=*|os-version=*|arch=*) pv[${b%%=*}]=${b#*=} ;;
      *) echo "PLATFORM: $b binds none of $PLATFORM_VARS" >&2; return 1 ;;
    esac
  done
  for v in $PLATFORM_VARS; do s+=${s:+,}$v=${pv[$v]}; done
  printf '%s\n' "$s"
}
PLATFORM=$(platform_whole "${PLATFORM:-}") || exit 2

root_platform() {  # with OPAMROOT set
  local v x s=
  for v in $PLATFORM_VARS; do
    x=$(opam var "$v" 2> /dev/null) || return 1
    s+=${s:+,}$v=$x
  done
  printf '%s\n' "$s"
}
