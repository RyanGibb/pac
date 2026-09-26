# Sourced by scale.sh, check.sh and seed.sh: npm as each runs it, against
# the shim on PORT and with the scratch HOME, cache and config setup.sh
# builds under NPM_RUN, so that no global config, ~/.npmrc or global cache
# reaches a run.  npm runs NPM_GIT as git (default: none).  NPM_TIMEOUT
# bounds it where the caller is not itself under a timeout(1), whose kill
# would not reach a second one's process group.
npm_in() {  # <dir> <npm args...>
  (cd "$1" && shift && HOME="$NPM_RUN/home" npm_config_git=${NPM_GIT:-false} \
     ${NPM_TIMEOUT:+timeout "$NPM_TIMEOUT"} npm "$@" \
     --registry "http://127.0.0.1:$PORT" --cache "$NPM_RUN/home/npmcache" \
     --userconfig "$NPM_RUN/home/.npmrc" --globalconfig "$NPM_RUN/home/npmrc-global" \
     --no-audit --no-fund --no-update-notifier)
}
