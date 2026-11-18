#!/bin/sh
set -eu
cd "$(dirname "$0")"
lean_bin=${LEAN:-lean}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true Identifiable.lean
patch -s -o "$tmp/Changed.lean" Identifiable.lean < mutation.patch
if "$lean_bin" -DwarningAsError=true "$tmp/Changed.lean" >"$tmp/control.log" 2>&1; then
  echo "Modified claim passed unexpectedly" >&2
  exit 1
fi
grep -q 'Changed.lean:.*error:' "$tmp/control.log"
echo "Rejected control: substitute an unobserved endpoint."
