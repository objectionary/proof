<!--
SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
SPDX-License-Identifier: MIT
-->

# Confluence of φ-Calculus Normalization (Lean 4)

A complete, machine-checked proof — in [Lean 4](https://leanprover.github.io) — that the
normalization (reduction) rules of the φ-calculus are **confluent (Church–Rosser)**: the order in
which the rules fire never changes the result. It is about the calculus as implemented by the
reference manipulator [`phino`][phino] — the same eleven rules the [paper][paper]'s Fig. 4 is
generated from — and supersedes the earlier minimal/extended development kept in this repository's
history (which finished only the minimal calculus).

**`#print axioms PhiConfluence.confluence` = `[propext, Quot.sound]`** — no `sorry`, no
`Classical.choice`.

## The theorem

`⟶` is the compatible (congruence) closure of the eleven `phino` rules
(`dd, dc, null, over, stop, miss, stay, phi, alpha, dot, copy`) over `Term`. `PhiConfluence.confluence`:

> For all **well-formed** `e`, if `e ⟶* e₁` and `e ⟶* e₂`, then there exists `e₃` with `e₁ ⟶* e₃`
> and `e₂ ⟶* e₃`.

It is proved via **parallel reduction** and the **Takahashi diamond** (mathlib's
`Relation.church_rosser`); the system is non-terminating (`⟦x↦y,y↦x⟧.x` diverges), so Newman's lemma
does not apply.

**Scope.** The `WF e` hypothesis re-imposes the paper's own grammar (unique keys; `αᵢ` is not a
formation key) that the deliberately-looser `Binding` encoding drops — it is *necessary*, since
without it `alpha` and `over` form a non-joinable critical pair. The implicit parent attribute `ρ`
that the paper and phino give every formation is modelled (`canon`), so the result governs phino's
actual term space. `λ`/`Δ` atoms are not part of `⟶` — their evaluation is the paper's *separate*,
stateful Morphing/Dataization functions, not term rewriting. The frozen contract is in
[`docs/M0-spec.md`](docs/M0-spec.md); the design and provenance in [`docs/DESIGN.md`](docs/DESIGN.md).

## Verify it yourself

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh   # one-time: Lean's toolchain manager
lake exe cache get          # download mathlib's prebuilt artifacts
lake build                  # green ⇒ every theorem is kernel-checked (CI also gates #print axioms)
lake exe demo               # the eleven rules + example reductions, by the project's own reducer
bash scripts/difftest.sh    # our reducer vs `phino rewrite --normalize` (needs phino on PATH)
```

The displayed rule table (`Rules.lean`) is generated from phino's `resources/*.yaml` — the same
source the paper's Fig. 4 renders from — so it cannot drift from phino. `reduce_sound` certifies
that every step the runnable reducer takes is a genuine `Step`, and `difftest` confirms our
reducer's normal forms match phino's. Run `#print axioms <name>` on any result to inspect its axiom
footprint.

## How it fits together

```
Main.lean / Difftest.lean         demo + phino differential test
PhiConfluence/
  Syntax · Attributes · WellFormed  Term/Binding/Attr; lookup/fill/voidAtOrdinal; the WF predicate
  Step                              the relation ⟶ — eleven rules + congruence closure
  Nf · Normal                       structural normal form (the counterpart of phino's isNF)
  Context · Canonical               contextualization C(e⊳ctx); the implicit-ρ canonicalisation
  Parallel                          Par/ParB, complete development `devel`, the Takahashi triangle
  Preservation · Diamond            WF preserved under reduction; the WF-relativized diamond
  Confluence                        the headline `confluence`
  Equivalence                       `≡` (convertibility) as an Equivalence on well-formed terms
  Reduce · Render · Rules           executable reducer + reduce_sound; pretty-printer; rule table
  Abstract/Rewriting                Diamond / Confluent vocabulary + the church_rosser bridge
docs/      M0-spec.md (frozen contract) · DESIGN.md (design + provenance)
scripts/   gen-rules.py · regen-rules.sh · difftest.sh · confluence-probe.sh
```

## Stack

Lean 4 (`leanprover/lean4:v4.30.0`) and mathlib4 (pinned in `lakefile.toml`), built with Lake.
Abstract rewriting is built on mathlib's `Prop`-valued `Relation` API. CI runs `lake build` with a
`#print axioms` gate, the phino differential test, a rule-table-in-sync check, and the standard
objectionary hygiene checks.

[paper]: https://github.com/objectionary/calculus-paper
[phino]: https://github.com/objectionary/phino
