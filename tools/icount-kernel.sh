#!/bin/bash
# Count the instructions the Lean kernel spends checking `EXPR = VALUE`.
#
# usage (run inside a problem's lake workspace, after `lake build MODULE`):
#   tools/icount-kernel.sh MODULE 'Submission.impl 50' 15
#
# Only work inside `lean_elab_add_decl` (the kernel) is counted, so the Mathlib
# import and elaboration don't add noise; repeated runs agree to ~0.1%.
# Includes a fixed baseline (~0.5M for a `Nat` result, ~0.8M for `Int`).
# Against the official playground numbers so far:
#   official ≈ 0.907 × local − 0.40M
source ~/.elan/env
LP=$(lake env printenv LEAN_PATH); LEANBIN=$(elan which lean)
f=$(mktemp -p . KXXXX.lean)
printf "import %s\nset_option maxRecDepth 100000\ntheorem t : %s = %s := by decide +kernel\n" "$1" "$2" "$3" > "$f"
LEAN_PATH=$LP valgrind --tool=callgrind --toggle-collect='lean_elab_add_decl*' \
  --callgrind-out-file=/dev/null "$LEANBIN" "$f" 2>&1 | grep -oE 'refs: +[0-9,]+' | tr -d ', ' | cut -d: -f2
rm -f "$f"
