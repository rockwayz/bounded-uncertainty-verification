#!/bin/bash
# Fast local type-check against a prebuilt mathlib checkout, without invoking lake
# (lake would re-resolve dependencies; the checkout's oleans are already built).
# Set MATHLIB_DIR to your mathlib4 checkout (default: ~/mathlib4). It must be built
# with the toolchain named in ./lean-toolchain, from which the lean binary is derived
# via elan's toolchain directory layout.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
M="${MATHLIB_DIR:-$HOME/mathlib4}"
TC_SPEC="$(cat "$DIR/lean-toolchain")"
TC="${ELAN_HOME:-$HOME/.elan}/toolchains/$(printf '%s' "$TC_SPEC" | sed -e 's|/|--|g' -e 's|:|---|g')/bin/lean"
LP="$M/.lake/build/lib/lean"
for p in "$M"/.lake/packages/*/; do
  [ -d "$p.lake/build/lib/lean" ] && LP="$LP:$p.lake/build/lib/lean"
done
exec env LEAN_PATH="$LP" "$TC" "${1:-VCalc/Basic.lean}"
