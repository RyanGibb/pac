# apk's exit counts its errors, so the refusal is read off the error alone
refused() {  # <rc> <log>
  grep -qE -f "$S/refusals" "$2"
}
