#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Confluence de-risking spike for the FULL phino calculus (all 11 rules), run before
# investing in the M3/M4 Lean diamond. For each φ-program it computes the default normal
# form and then tries to reach a DIFFERENT finite normal form two complementary ways;
# two distinct finite normal forms ⇒ a confluence counterexample.
#
#   (1) Rule-order check  — `phino rewrite --normalize --shuffle` ITERS times. `--shuffle`
#       varies RULE ORDER only (and the nf-guards make normalization near-deterministic),
#       so agreement here is weak evidence.
#   (2) Off-strategy redex-position check — for each rule R, force R to fire FIRST via a
#       bounded single-rule application (`--rule resources/R.yaml --max-depth 1
#       --max-cycles 1`), then re-normalize that reduct. This drives the term down a
#       different first step (a different rule, and usually a different POSITION) than
#       phino's built-in strategy, probing LOCAL CONFLUENCE — the property the diamond
#       rests on. Reaches paths `--shuffle` cannot.
#
# Non-termination is detected with `--depth-sensitive` (phino exits non-zero when
# rewriting does not finish within its cycle bound); such unfinished paths are NOT
# counterexamples and are excluded. A real counterexample needs TWO distinct FINITE
# normal forms. Agreement across both checks is moderate (not conclusive) evidence; the
# conclusive artifact is the Lean diamond proof. See docs/DESIGN.md §7.
#
# Usage: bash scripts/confluence-probe.sh [extra-corpus-dir ...]
#        ITERS=32 PHINO_RESOURCES=/path/to/phino/resources bash scripts/confluence-probe.sh

set -uo pipefail
cd "$(dirname "$0")/.."
ITERS="${ITERS:-24}"

command -v phino >/dev/null 2>&1 || { echo "phino not on PATH; skipping" >&2; exit 0; }
PHINO_VERSION="$(cat .phino-version)"

RESOURCES="${PHINO_RESOURCES:-}"
if [ -z "$RESOURCES" ]; then
  for cand in /Users/maxonfjvipon/code/haskell/phino/resources /tmp/phino_ref/resources; do
    [ -d "$cand" ] && RESOURCES="$cand" && break
  done
fi

TO=""
if command -v gtimeout >/dev/null 2>&1; then TO="gtimeout 10"
elif command -v timeout >/dev/null 2>&1; then TO="timeout 10"; fi

RULES="alpha copy dc dd dot miss null over phi stay stop"
diverged=0
total=0

# Normal form of a file, or the sentinel <diverge>/<error> for an unfinished/failed run.
norm() {
  local out ec
  out=$($TO phino rewrite --pin="$PHINO_VERSION" --normalize --depth-sensitive --flat "$1" 2>&1); ec=$?
  if [ "$ec" = 124 ]; then echo "<diverge>"
  elif [ "$ec" = 0 ]; then echo "$out"
  elif printf '%s' "$out" | grep -q 'depth-sensitive'; then echo "<diverge>"
  else echo "<error>"; fi
}

# Collect the FINITE normal forms reachable from a program along several paths (default,
# rule-order shuffles, and off-strategy single-rule first-steps). A confluence
# counterexample is TWO DISTINCT finite normal forms; divergent paths contribute nothing
# (a term may be confluent yet have both a normal form and an infinite path).
probe() {
  local file="$1" label="$2"
  total=$((total + 1))
  local samples=()

  local nf0; nf0=$(norm "$file")
  case "$nf0" in "<diverge>"|"<error>") : ;; *) samples+=("default	$nf0") ;; esac

  local i s ec
  for ((i = 1; i <= ITERS; i++)); do
    s=$($TO phino rewrite --pin="$PHINO_VERSION" --normalize --shuffle --depth-sensitive --flat "$file" 2>&1); ec=$?
    [ "$ec" = 0 ] && [ -n "$s" ] && samples+=("shuffle	$s")
  done

  local canon; canon=$($TO phino rewrite --pin="$PHINO_VERSION" --flat "$file" 2>&1)
  local rule forced nfr tmp
  tmp="$(mktemp)"
  for rule in $RULES; do
    [ -f "$RESOURCES/$rule.yaml" ] || continue
    forced=$($TO phino rewrite --pin="$PHINO_VERSION" --rule "$RESOURCES/$rule.yaml" --max-depth 1 --max-cycles 1 --flat "$file" 2>&1)
    { [ -z "$forced" ] || [ "$forced" = "$canon" ]; } && continue
    printf '%s\n' "$forced" > "$tmp"
    nfr=$(norm "$tmp")
    case "$nfr" in "<diverge>"|"<error>") continue ;; esac
    samples+=("force:$rule	$nfr")
  done
  rm -f "$tmp"

  if [ "${#samples[@]}" -eq 0 ]; then
    echo "SKIP  (no finite normal form on any path)    $label"; return
  fi
  local distinct n
  distinct=$(printf '%s\n' "${samples[@]}" | cut -f2- | LC_ALL=C sort -u)
  n=$(printf '%s\n' "$distinct" | grep -c .)
  if [ "$n" -le 1 ]; then
    echo "OK    (1 NF over ${#samples[@]} paths)            $label"
  else
    echo "DIVERGENCE !! ($n distinct normal forms)      $label"
    printf '%s\n' "${samples[@]}" | LC_ALL=C sort -t'	' -k2 | sed 's/^/        /'
    diverged=1
  fi
}

if [ -z "$RESOURCES" ]; then
  echo "note: phino resources/ not found — running rule-order check only (set PHINO_RESOURCES for the off-strategy check)" >&2
fi

# Crafted stressors: nf-guard non-monotonicity (inner reduction enabling outer dot/copy),
# ρ-feedback, decorator-φ, nested dot/copy — the cases that endanger the diamond.
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
i=0
for prog in \
  '{[[ a -> [[ x -> [[ t -> [[]] ]].t ]].x ]]}' \
  '{[[ k -> ?, r -> $.k ]](k -> [[]]).r}' \
  '{[[ @ -> [[ x -> [[]] ]] ]].x}' \
  '{[[ x -> $.y, y -> [[]] ]].x}' \
  '{[[ x -> [[ y -> [[ z -> [[]] ]].z ]].y ]].x}' \
  '{[[ x -> [[ a -> ^ ]] ]].x}' \
  '{[[ d -> ?, e -> [[ b -> $.b ]].b ]].d}'
do
  i=$((i + 1)); printf '%s\n' "$prog" > "$tmp/crafted-$i.phi"
  probe "$tmp/crafted-$i.phi" "crafted-$i  $prog"
done

for dir in "$@"; do
  [ -d "$dir" ] || continue
  for f in "$dir"/*.phi; do
    [ -e "$f" ] || continue
    probe "$f" "$f"
  done
done

echo "----"
if [ "$diverged" -eq 0 ]; then
  echo "No divergence across $total programs (rule-order + off-strategy redex-position checks)."
  echo "Moderate positive evidence — the conclusive artifact is the Lean diamond proof (docs/DESIGN.md §7)."
else
  echo "DIVERGENCE FOUND — a confluence counterexample candidate (investigate above)."
fi
exit "$diverged"
