#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean_bin=${LEAN:-lean}
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build"
mkdir -p "$build/SoftwareIsQuantifiable"
"$lean_bin" -DwarningAsError=true -o "$build/SoftwareIsQuantifiable/Coverage.olean" "SoftwareIsQuantifiable/Coverage.lean" >/dev/null
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true examples/LedgerRepair.lean
sh examples/range-ledger/check.sh
