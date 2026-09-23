#!/usr/bin/env python3
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
"""
Generate PhiConfluence/RuleData.lean from phino's resources/*.yaml.

Unlike `gen-rules.py` (which emits *display strings* for the demo), this emits the
**structured** rule data: each rule becomes a `RuleEntry` of typed tags (redex shape,
side-conditions, contractum), whose types are defined in PhiConfluence/RuleSchema.lean.
The CI build regenerates PhiConfluence/RuleData.lean from pinned phino and then compiles
it, so the proof always builds against phino-derived rules and a phino change that breaks
compilation (or trips the fidelity lock below) fails the build.

DESIGN — a *fidelity lock*, not a general translator.
  phino's rule semantics live in its Haskell (`contextualize`, `isNF`, ordinals …),
  not in the YAML, so the YAML cannot be mechanically translated into a Lean relation.
  Instead this script carries one *locked interpretation*
  per rule (the structured tags below) and ASSERTS that phino's current YAML still
  renders to the pattern/result/condition this interpretation assumes — failing loudly
  on any mismatch. The locked tags are emitted into RuleData.lean, which the CI build
  regenerates from pinned phino and compiles — so phino-drift trips this assertion and
  fails the build.

The `when`/`where` rendering comes from `phino_render.py`, the same module `gen-rules.py`
uses, so the asserted condition strings are exactly the display table's.

Usage:
    gen-rule-data.py <phino-resources-dir> <output-RuleData.lean>
"""
import re
import sys

from phino_render import rules as rendered


def norm(s):
    """Whitespace-insensitive comparison key (phino's pattern strings have stray spaces)."""
    return re.sub(r"\s+", " ", s or "").strip()


# --- the locked interpretation: one entry per phino rule -------------------------------
#
# Each entry asserts phino's rendered (pattern, result, cond, where) and, on a match,
# contributes the structured Lean tags. `shape`/`conds`/`rhs` are Lean `RuleEntry` field
# expressions; they MUST stay in step with PhiConfluence/RuleSchema.lean's inductives.
# `expect` strings are phino's YAML as `phino_render.py` renders it (== the gen-rules.py table).
#
# If phino's YAML drifts from `expect`, this script aborts (see `check`) — that is the
# point. The tags themselves are not yet checked against `Step`: no conformance theorem
# exists so far. Adding/removing a phino rule trips the name-set assertion in `main`.

LOCK = {
    "dd": dict(
        expect=("⊥.𝜏", "⊥", "", ""),
        shape=".dispatchBot", conds="[]", rhs=".bot"),
    "dc": dict(
        expect=("⊥(𝜏 ↦ 𝑒)", "⊥", "", ""),
        shape=".appBot", conds="[]", rhs=".bot"),
    "null": dict(
        expect=("⟦𝐵1, 𝜏 ↦ ∅, 𝐵2⟧.𝜏", "⊥", "", ""),
        shape=".dispatchForm", conds="[.slotVoid]", rhs=".bot"),
    "over": dict(
        expect=("⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧(𝜏 ↦ 𝑒2)", "⊥", "¬(𝜏 = ρ)", ""),
        shape=".appForm", conds="[.slotAttached, .attrNeRho]", rhs=".bot"),
    "stop": dict(
        expect=("⟦𝐵⟧.𝜏", "⊥", "¬(𝜏 ∈ 𝐵) and ¬(φ ∈ 𝐵) and ¬(λ ∈ 𝐵)", ""),
        shape=".dispatchForm", conds="[.slotAbsent, .phiAbsent, .noLambda]", rhs=".bot"),
    "miss": dict(
        expect=("⟦𝐵⟧(𝜏 ↦ 𝑒)", "⊥", "¬(𝜏 ∈ 𝐵) and ¬(α-attr(𝜏))", ""),
        shape=".appForm", conds="[.slotAbsent, .attrNotAlpha]", rhs=".bot"),
    "stay": dict(
        expect=("⟦𝐵1, ρ ↦ 𝑒1, 𝐵2⟧(ρ ↦ 𝑒2)", "⟦𝐵1, ρ ↦ 𝑒1, 𝐵2⟧", "", ""),
        shape=".appForm", conds="[.attrIsRho, .slotAttached]", rhs=".formSame"),
    "phi": dict(
        expect=("⟦𝐵⟧.𝜏", "⟦𝐵⟧.φ.𝜏", "φ ∈ 𝐵 and ¬(𝜏 ∈ 𝐵)", ""),
        shape=".dispatchForm", conds="[.phiPresent, .slotAbsent]", rhs=".phiExpand"),
    "alpha": dict(
        expect=("⟦𝐵1, 𝜏1 ↦ ∅, 𝐵2⟧(𝜏2 ↦ 𝑒)", "⟦𝐵1, 𝜏1 ↦ ∅, 𝐵2⟧(𝜏1 ↦ 𝑒)",
                "index(𝜏2) = domain(𝐵1)", ""),
        shape=".appForm", conds="[.alphaVoidOrdinal]", rhs=".alphaRename"),
    "dot": dict(
        expect=("⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧.𝜏", "𝑒2(ρ ↦ ⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧)", "nf(𝑒1)",
                "𝑒2 := contextualize(𝑒1, ⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧)"),
        shape=".dispatchForm", conds="[.slotAttached, .valNf]", rhs=".dotFeedback"),
    # NOTE — copy keeps phino's `xi-free` guard in the DATA (Step.copy carries `xiFree`);
    # only the DISPLAY table (gen-rules.py) strips ξ for paper-figure parity.
    "copy": dict(
        expect=("⟦ 𝐵1, 𝜏 ↦ ∅, 𝐵2 ⟧(𝜏 ↦ 𝑒)", "⟦ 𝐵1, 𝜏 ↦ 𝑒, 𝐵2 ⟧",
                "xi-free(𝑒) and nf(𝑒)", ""),
        shape=".appForm", conds="[.slotVoid, .argXiFree, .argNf]", rhs=".copyFill"),
}


def check(name, got, want):
    g = tuple(norm(x) for x in got)
    w = tuple(norm(x) for x in want)
    if g != w:
        raise SystemExit(
            f"FIDELITY-LOCK BREACH for rule '{name}': phino's YAML no longer matches the "
            f"locked interpretation in gen-rule-data.py.\n  phino : {g}\n  locked: {w}\n"
            f"Re-read the phino rule, update LOCK['{name}'] and its tags, and check by hand "
            f"that `Step` in PhiConfluence/Step.lean still matches, since no conformance "
            f"theorem ties the tags to `Step` yet")


def main():
    if len(sys.argv) != 3:
        raise SystemExit("Usage: gen-rule-data.py <phino-resources-dir> <output-RuleData.lean>")
    res_dir, out = sys.argv[1], sys.argv[2]
    found = {}
    for r in rendered(res_dir):
        name = r["name"]
        if name in found:
            raise SystemExit(f"duplicate rule name '{name}' in {res_dir}")
        if name not in LOCK:
            raise SystemExit(f"phino has an UNLOCKED rule '{name}' — add it to LOCK and to Step")
        check(name, (r["pattern"], r["result"], r["cond"], r["wher"]), LOCK[name]["expect"])
        found[name] = LOCK[name]
    missing = set(LOCK) - set(found)
    if missing:
        raise SystemExit(f"locked rules absent from phino's resources: {sorted(missing)}")
    lines = [
        # REUSE-IgnoreStart
        "-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com",
        "-- SPDX-License-Identifier: MIT",
        # REUSE-IgnoreEnd
        "",
        "-- AUTO-GENERATED by .github/gen-rule-data.py from objectionary/phino resources/*.yaml.",
        "-- Not tracked by Git: `bash .github/regen-rules.sh` regenerates it from pinned phino.",
        "",
        "import PhiConfluence.RuleSchema",
        "",
        "/-!",
        "# Normalization rules as structured data, generated from phino",
        "",
        "The eleven rules as `RuleEntry` tags (types in PhiConfluence/RuleSchema.lean), emitted",
        "by the fidelity-lock deriver `.github/gen-rule-data.py`. This file is not tracked by",
        "Git: it is regenerated from pinned phino before every build.",
        "-/",
        "",
        "namespace PhiConfluence",
        "",
        "/-- The φ-calculus normalization rules as structured, interpretable data. -/",
        "def normalizationRuleData : List RuleEntry :=",
    ]
    entries = []
    for name in sorted(found):
        e = found[name]
        entries.append(
            '  { name := "%s", shape := %s, conds := %s, rhs := %s }'
            % (name, e["shape"], e["conds"], e["rhs"]))
    lines.append("  [ " + "\n  , ".join(x.strip() for x in entries) + " ]")
    lines.append("")
    lines.append("end PhiConfluence")
    lines.append("")
    with open(out, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    print(f"wrote {out} with {len(found)} rules (fidelity lock held)")


if __name__ == "__main__":
    main()
