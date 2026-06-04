#!/usr/bin/env python3
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
"""
Generate PhiConfluence/RuleData.lean from phino's resources/*.yaml.

Unlike `gen-rules.py` (which emits *display strings* for the demo), this emits the
**structured** rule data the proof is pinned against: each rule becomes a `RuleSpec`
of typed tags (redex shape, side-conditions, contractum) that the hand-written
interpreter `applies` (PhiConfluence/RuleSchema.lean) gives a semantics to, and that
`conformance` (PhiConfluence/RuleConform.lean) proves equal to the `Step` relation.
So if phino changes a rule, the regenerated data changes and the Lean conformance
theorem stops type-checking — drift between phino and the proof becomes a build error.

DESIGN — a *fidelity lock*, not a general translator.
  phino's rule semantics live in its Haskell (`contextualize`, `isNF`, ordinals …),
  not in the YAML, so the YAML cannot be mechanically translated into a Lean relation.
  Instead this script carries one *locked interpretation*
  per rule (the structured tags below) and ASSERTS that phino's current YAML still
  renders to the pattern/result/condition this interpretation assumes — failing loudly
  on any mismatch. The locked tags are emitted; the proof checks them against `Step`.
  Net: phino-drift trips the assertion here (CI red); a tags-vs-`Step` mismatch trips
  the Lean conformance theorem. Both ends are pinned.

This intentionally duplicates `gen-rules.py`'s `when`/`where` rendering (keep in sync) so
the asserted condition strings match the display table's — one rendering, two consumers.

Usage:
    gen-rule-data.py <phino-resources-dir> <output-RuleData.lean>
"""
import glob
import os
import re
import sys

import yaml


# --- condition/where rendering: identical to gen-rules.py (kept in sync on purpose) ---

def rterm(x):
    return str(x)


def rcmp(x):
    if isinstance(x, dict):
        k = next(iter(x))
        v = x[k]
        if k == "index":
            return f"index({rterm(v)})"
        if k == "length":
            return f"|{rterm(v)}|"
        if k == "domain":
            return f"domain({rterm(v)})"
        return f"{k}({rterm(v)})"
    return rterm(x)


def rcond(w):
    if w is None:
        return ""
    if not isinstance(w, dict):
        return rterm(w)
    k = next(iter(w))
    v = w[k]
    if k == "and":
        return " and ".join(p for p in (rcond(x) for x in v) if p)
    if k == "or":
        return " or ".join(p for p in (rcond(x) for x in v) if p)
    if k == "not":
        return "¬(" + rcond(v) + ")"
    if k == "in":
        return f"{rterm(v[0])} ∈ {rterm(v[1])}"
    if k == "nf":
        return f"nf({rterm(v)})"
    if k == "alpha":
        return f"α-attr({rterm(v)})"
    if k == "eq":
        return f"{rcmp(v[0])} = {rcmp(v[1])}"
    return f"{k}({rterm(v)})"


def rwhere(ws):
    parts = []
    for w in ws or []:
        meta = w.get("meta")
        fn = w.get("function")
        args = w.get("args", [])
        parts.append(f"{meta} := {fn}({', '.join(rterm(a) for a in args)})")
    return " and ".join(parts)


def norm(s):
    """Whitespace-insensitive comparison key (phino's pattern strings have stray spaces)."""
    return re.sub(r"\s+", " ", s or "").strip()


# --- the locked interpretation: one entry per phino rule -------------------------------
#
# Each entry asserts phino's rendered (pattern, result, cond, where) and, on a match,
# contributes the structured Lean tags. `shape`/`conds`/`rhs` are Lean `RuleSpec` field
# expressions; they MUST stay in step with PhiConfluence/RuleSchema.lean's inductives.
# `expect` strings are phino's current YAML as rendered above (== the gen-rules.py table).
#
# If phino's YAML drifts from `expect`, this script aborts (see `check`) — that is the
# point. If the *interpretation* (tags) is what changed, the Lean `conformance` theorem
# is what fails. Adding/removing a phino rule trips the name-set assertion in `main`.

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
            f"Re-read the phino rule, update LOCK['{name}'] AND the matching tags, and "
            f"re-verify PhiConfluence/RuleConform.lean's `conformance` against `Step`.")


def main():
    if len(sys.argv) != 3:
        raise SystemExit("Usage: gen-rule-data.py <phino-resources-dir> <output-RuleData.lean>")
    res_dir, out = sys.argv[1], sys.argv[2]
    found = {}
    for path in sorted(glob.glob(os.path.join(res_dir, "*.yaml"))):
        with open(path, encoding="utf-8") as f:
            d = yaml.safe_load(f)
        name = str(d["name"])
        if name in found:
            raise SystemExit(f"duplicate rule name '{name}' in {res_dir}")
        got = (str(d["pattern"]), str(d["result"]), rcond(d.get("when")), rwhere(d.get("where")))
        if name not in LOCK:
            raise SystemExit(f"phino has an UNLOCKED rule '{name}' — add it to LOCK and to Step/conformance")
        check(name, got, LOCK[name]["expect"])
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
        "-- AUTO-GENERATED by scripts/gen-rule-data.py from objectionary/phino resources/*.yaml.",
        "-- DO NOT EDIT BY HAND. Regenerate after phino's rules change.",
        "",
        "import PhiConfluence.RuleSchema",
        "",
        "/-!",
        "# Normalization rules as structured data, generated from phino",
        "",
        "The eleven rules as `RuleSpec` tags, emitted by the fidelity-lock deriver",
        "`scripts/gen-rule-data.py`. `PhiConfluence.RuleConform.conformance` proves this list",
        "equal to the `Step` relation, so a phino change that survives the deriver's assertions",
        "but alters a rule's meaning makes that theorem fail to compile.",
        "-/",
        "",
        "namespace PhiConfluence",
        "",
        "/-- The φ-calculus normalization rules as structured, interpretable data. -/",
        "def normalizationRuleData : List RuleSpec :=",
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
