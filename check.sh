#!/bin/bash
# Type-check the module against the prebuilt local mathlib, without invoking lake
# (lake would try to re-resolve deps; the oleans in ../mathlib4 are already built).
set -uo pipefail
M=/Users/talrock/mathlib4
TC=/Users/talrock/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/bin/lean
LP="$M/.lake/build/lib/lean"
for p in "$M"/.lake/packages/*/; do
  [ -d "$p.lake/build/lib/lean" ] && LP="$LP:$p.lake/build/lib/lean"
done
exec env LEAN_PATH="$LP" "$TC" "${1:-VCalc/Basic.lean}"
