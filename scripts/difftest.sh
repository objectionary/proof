#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Differential test: for each example program, check that phino's normal form
# (`phino rewrite --normalize`) equals our reducer's normal form. The behavioral
# pin between this prover's Step relation and phino. Requires `phino` on PATH.

set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

if ! command -v phino >/dev/null 2>&1; then
  echo "FATAL: phino not found on PATH; the differential test requires it (fail-fast, not skip)" >&2
  exit 1
fi

lake build difftest >/dev/null 2>&1 || { echo "failed to build difftest" >&2; exit 1; }

fail=0
count=0
while IFS=$'\t' read -r input expected; do
  [ -z "${input:-}" ] && continue
  count=$((count + 1))
  out=$(printf '%s\n' "$input" | phino rewrite --normalize --flat 2>/dev/null)
  pn=$(printf '%s' "$out" | tr -d '[:space:]'); pn=${pn#Φ↦}
  ours=$(printf '%s' "$expected" | tr -d '[:space:]')
  if [ "$pn" = "$ours" ]; then
    echo "PASS  $input    ↝*  $expected"
  else
    echo "FAIL  $input    phino=[$out]  ours=[$expected]"
    fail=1
  fi
done < <(lake exe difftest 2>/dev/null)

echo "----"
if [ "$fail" -eq 0 ]; then
  echo "All $count differential checks passed (our reducer agrees with phino)."
else
  echo "Some differential checks FAILED."
fi
exit $fail
