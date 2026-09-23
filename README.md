<!--
SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
SPDX-License-Identifier: MIT
-->

# Confluence of φ-Calculus Normalization (Lean 4)

[![build](https://github.com/objectionary/proof/actions/workflows/build.yml/badge.svg)](https://github.com/objectionary/proof/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](https://github.com/objectionary/proof/blob/master/LICENSE.txt)

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
pip install -r .github/requirements.txt                  # one-time: Python deps of the generators
make                        # green ⇒ every theorem is kernel-checked and axiom-clean, as in CI
lake exe demo               # the eleven rules + example reductions, by the project's own reducer
make difftest               # our reducer vs `phino rewrite --normalize` (needs phino on PATH)
```

`make` needs GNU Make 4.3 or newer. It fetches mathlib's prebuilt artifacts, generates the rule
files from pinned phino (and regenerates them only when `.phino-version` or a generator changes),
runs the generator unit tests and `lake build`, and checks that no headline theorem depends on a
forbidden axiom.

The rule files (`Rules.lean`, `RuleData.lean`) are not kept in Git: they are generated from the
`resources/*.yaml` of the phino pinned in `.phino-version` — the same source the paper's Fig. 4
renders from — so they cannot drift from phino. `reduce_sound` certifies
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
  RuleSchema · RuleData             rule tags generated from phino by the fidelity lock
  Abstract/Rewriting                Diamond / Confluent vocabulary + the church_rosser bridge
docs/      M0-spec.md (frozen contract) · DESIGN.md (design + provenance)
.github/   regen-rules.sh · gen-rules.py · gen-rule-data.py · phino_render.py · difftest.sh
           test_*.py (generator unit tests) · axioms.lean · requirements.txt · workflows/
Makefile   `make` builds and checks everything CI checks, except difftest
```

## Stack

Lean 4 (`leanprover/lean4:v4.30.0`) and mathlib4 (pinned in `lakefile.toml`), built with Lake.
Abstract rewriting is built on mathlib's `Prop`-valued `Relation` API. CI runs `make` (unit tests,
`lake build`, and a `#print axioms` gate), the phino differential test, and the standard
objectionary hygiene checks.

[paper]: https://github.com/objectionary/calculus-paper
[phino]: https://github.com/objectionary/phino
