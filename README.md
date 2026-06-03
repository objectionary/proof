<!--
SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
SPDX-License-Identifier: MIT
-->

# Confluence of φ-Calculus Normalization (Lean 4)

A fresh, machine-checked proof — in [Lean 4](https://leanprover.github.io) — that the
normalization (reduction) rules of the current [φ-calculus][paper] are **confluent**
(Church–Rosser). It targets the calculus of the reference manipulator [`phino`][phino] —
the same eleven rules the [paper][paper]'s Fig. 4 is generated from — not the older minimal
calculus of the deprecated [`objectionary/proof`][oldproof].

**Scope.** The result is `WF`-scoped (necessary once `alpha` is present — see below). The paper
(`foundations.tex`, Def. Parent) and phino put an implicit void parent (`ρ`) in *every* formation;
**this is now modelled** — `canon` injects it exactly as phino does (appended where absent,
recursive), and the result is proved canonical (`canon_canonical`), well-formed (`wf_canon`), and
**closed under reduction** (`step_canonical` — phino's term space stays put). So the headline
governs **phino's actual calculus**, not a `ρ`-free fragment: `difftest` now agrees with phino on
real formation results, including the cases that used to diverge (`⟦⟧(ρ↦Φ)↝⟦ρ↦Φ⟧`, the
`alpha`-to-`ρ` case). Full detail in [`docs/DESIGN.md`](docs/DESIGN.md) §9.

This README is a **guide: what to run, and what you get.** For the full design and
rationale see [`docs/DESIGN.md`](docs/DESIGN.md); for the frozen theorem statement and the
rule⇄constructor table see [`docs/M0-spec.md`](docs/M0-spec.md).

## Quick start — what to do and what you get

**1. Build it.**

```bash
# one-time: install Lean's toolchain manager
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
lake exe cache get   # download mathlib's prebuilt artifacts (avoids ~1h compile)
lake build           # → "Build completed successfully", zero sorry/axiom
```

> **What you get:** a green build means *every definition and theorem in the project
> is checked by Lean's kernel* — no gaps, no `sorry`, no extra axioms.

**2. See the rules and reductions.**

```bash
lake exe demo
```

> **What you get:** the eleven normalization rules **generated from phino's
> `resources/*.yaml`** — the same source the paper's Fig. 4 is rendered from — printed
> in the paper's Unicode notation so you can compare them directly; followed by example
> φ-programs reduced step-by-step by *this project's own reducer* (e.g.
> `⊥.x.y ↝ ⊥.y ↝ ⊥`).

**3. Check that our logic agrees with phino.**

```bash
bash scripts/difftest.sh    # requires `phino` on PATH
```

> **What you get:** for each example program this runs **both** `phino rewrite
> --normalize` *and* our reducer and confirms they reach the same normal form
> (`PASS`/`FAIL`, non-zero exit on any mismatch). This is the behavioral pin between the
> prover and phino — i.e. between the prover and the paper.

**4. Audit it yourself.**

* Read the source — the rules are in `PhiConfluence/Step.lean`; the Takahashi triangle in
  `Parallel.lean`; the headline `confluence` in `Confluence.lean` (and the diamond⇒confluence
  bridge in `Abstract/Rewriting.lean`).
* In any proof, run `#print axioms <name>`; a sorry-free proof lists at most
  `propext, Classical.choice, Quot.sound` — never `sorryAx`. (Ours in fact use only
  `propext` and `Quot.sound` — not even `Classical.choice`.)
* Regenerate the rule table straight from phino with
  `python3 scripts/gen-rules.py <phino>/resources PhiConfluence/Rules.lean`.

### What is proven today, and what is still ahead

**The headline is complete** (all eleven rules, `[propext, Quot.sound]`). Machine-checked and runnable *now*:

* the reduction relation `Step` for **all eleven rules** — the `⊥`-collapse six (`dd, dc, null,
  over, stop, miss`), `stay`, `phi`, `alpha` (positional `αᵢ`-renaming via `bs[i]?`), **`dot`**
  (`ρ`-feedback + contextualization — makes the system *non-terminating*), and **`copy`**
  (`⟦…τ↦∅…⟧(τ↦e₁) → ⟦…τ↦e₁…⟧`, guards `ξFree e₁` then `nf e₁` — a local slot-fill; under `ξ`-freeness
  the paper's `contextualize`/`scope` are provably the identity), with the full congruence closure;
* `reduce_sound` — every step the executable reducer takes is a genuine `Step` (soundness, so the
  demo is certified). The reducer implements **all eleven rules** and agrees with phino on every
  differential example (`scripts/difftest.sh`, **17/17**, all eleven rules incl. `alpha`). With the
  implicit parent modelled (`canon`), the corpus includes **real formation results that match phino
  exactly** — `⟦⟧(ρ↦Φ)↝⟦ρ↦Φ⟧`, the `alpha`-to-`ρ` case, and `ρ`-bearing normal forms — not just
  `⊥`-collapse outcomes;
* `Par`/`ParB` parallel reduction + `redMany_eq` (`ReflTransGen Step = ReflTransGen Par`),
  the total complete development `devel`/`develB`, and the **Takahashi triangle** `par_triangle`
  (`WF e → e ⇒ u → u ⇒ devel e`, **`WF`-scoped** now that `alpha` is present);
* **`WF.step` / `WF.par`** — reduction (single- and parallel-step) preserves well-formedness;
* **`confluence` — THE HEADLINE, `WF`-scoped Church–Rosser of the FULL calculus (all 11 rules)**:
  `WF e → e ↝∗ e₁ → e ↝∗ e₂ → ∃ e₃, e₁ ↝∗ e₃ ∧ e₂ ↝∗ e₃`. Proved through the WF-relativized
  diamond (`ParWF a b := WF a ∧ Par a b` → `parWF_diamond` → `Diamond.confluent` = mathlib's
  `church_rosser`, no termination → transported by `redMany_eq`). The `WF e` hypothesis re-imposes
  the paper's own grammar (unique keys; `αᵢ` not a formation key) that our looser `Binding` drops;
  it is necessary once `alpha` is present (the unconditional claim is false, so `step_confluent`
  was retired).

**`#print axioms confluence` = `[propext, Quot.sound]` — no `sorryAx`, no `Classical.choice`.** The
result the project set out to prove is complete: the eleven `phino` normalization rules are confluent
on well-formed terms. The diamond was additionally **de-risked** beforehand (no root critical pairs;
no divergence over a fixed corpus of 7 hand-crafted probe programs + the paper's Appendix-A
examples, under rule-order shuffling and an off-strategy single-rule check — `docs/DESIGN.md` §7;
this is a fixed corpus, not random fuzzing).

**Also done (the wrap):** the executable `reduceStep` now implements all eleven rules and
`difftest` agrees with phino **17/17** (all eleven rules incl. `alpha`); `nf_iff` (`nf ↔ ¬Reducible` on `WF` terms — the faithful
counterpart of phino's `isNF`); `≡` as an `Equivalence` (`conv_equivalence`). **Nothing remains
for the theorem:** `confluence` covers the entire normalization relation `⟶` as the current
paper/phino define it. (The paper's `λ`/`Δ` semantics live in its *separate* Morphing/Dataization
functions — stateful, not term rewriting, so outside `⟶`; see the scope note below.)

## What the headline theorem says (and the deliberate deviations)

The reduction relation `⟶` is the compatible (congruence) closure of the eleven `phino`
rules (`alpha, copy, dc, dd, dot, miss, null, over, phi, stay, stop`). The theorem
(`PhiConfluence.confluence`, proved for all eleven rules):

> for all **well-formed** `e` (`WF e`), if `e ⟶* e₁` and `e ⟶* e₂`, then there is `e₃`
> with `e₁ ⟶* e₃` and `e₂ ⟶* e₃`.

The `WF e` hypothesis re-imposes the paper's own grammar that our looser `Binding` drops. Of its two
clauses, **`αᵢ`-not-a-formation-key is *necessary*** for confluence: without it a malformed
`αᵢ`-keyed formation makes `alpha` and `over` a non-joinable critical pair, so the *unconditional*
statement is false once `alpha` is present (deviation #8). The **unique-key (`Nodup`) clause is
*faithfulness*** — it matches the paper's Def. Binding and aligns our `lookup` with phino's matcher
— carried but not used by the diamond argument. (Aside: phino's parser enforces unique keys but its
normalizer can emit duplicate-`ρ` formations — a phino bug; our model gives the well-formed answer.
See `docs/M0-spec.md` "Why `WF`-scoped".) The paper presupposes but never proves confluence; we
prove it, `WF`-scoped because our encoding is looser than the grammar.

Facts shaping the proof (full detail in `docs/M0-spec.md`):

* The system is **non-terminating** (`⟦x↦y,y↦x⟧.x` diverges), so Newman's lemma is
  unavailable. We prove confluence via **parallel reduction + the diamond property**
  (Tait–Martin-Löf / Takahashi), then transport it to `⟶*`.
* We follow phino's **disjoint** rule forms (which the current paper's Fig. 4 already
  uses, since it is generated from phino): `over` fires on an *attached* slot, `copy` on
  a *void* slot — avoiding the object-vs-`⊥` clash that a looser `τ∈b` reading (or the
  older v0.9.0 / arXiv-v9 rendering) would create.
* `dot`/`copy` carry **`nf` guards** (and `copy` an `ξ`-freeness guard) so each rule is
  single-path; this removes the `Rcopy`↔`Rdot` ordering ambiguity and the `Rcopy`/
  confluence circularity, at the cost of making `⟶` a *conditional* relation.
* **Outside the normalization relation `⟶`** (hence outside this theorem, by the paper's
  own structure): `λ`-atoms and `Δ`-data — their reduction is the paper's *separate*
  Morphing (`fig:morphing`) and Dataization (`fig:dataization`) partial functions (stateful,
  host-dependent), with no rule among the eleven; they sit as inert atoms. Also the older
  big-step `Rcopy` (superseded — the current paper's `copy` is the small-step form we use).

## Stack

* **Lean 4**, toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.30.0`).
* **mathlib4** pinned in `lakefile.toml` (`rev = v4.30.0`) — for `List`/`Decidable`,
  well-founded recursion, tactics, and `Relation` (`ReflTransGen`, `Join`,
  `church_rosser`).
* **Lake** build system; the displayed rule table is generated from phino's YAML by
  `scripts/gen-rules.py`.
* **Abstract rewriting** is built on mathlib's `Prop`-valued `Relation` API;
  `Abstract/Rewriting.lean` adds the `Diamond`/`Confluent` vocabulary and the
  `Diamond.confluent` bridge.

## Architecture (with status)

```
Main.lean                       -- `lake exe demo`: prints rules + reductions      [done]
Difftest.lean                   -- `lake exe difftest`: input ⟶ our-normal-form    [done]
PhiConfluence/
  Abstract/Rewriting.lean       -- Diamond, Confluent, Diamond.confluent           [done]
  Syntax.lean                   -- Term/Binding/Attr inductives                     [done]
  Attributes.lean               -- lookup, hasLambda, Attr.isAlpha, fill            [done]
  WellFormed.lean               -- WF/WFB predicate + domain (M3 well-formedness)   [done]
  Step.lean                     -- Step (⟶) + ↝/↝∗: all 11 rules + congruence         [done]
  Reduce.lean                   -- executable reduceStep + trace + reduce_sound     [done; all 11 rules]
  Render.lean                   -- Unicode pretty-printer + RuleSpec                [done]
  Rules.lean                    -- GENERATED rule table (from phino YAML)           [generated]
  Normal.lean                   -- Reducible/NormalForm + sink lemmas               [done]
  Nf.lean                       -- structural nf (11-rule normal form; dot/copy guard) [done, M4.3a]
  LocalConfluence.lean          -- reduction congruence-lifting + form inversion    [done; local_conf retired]
  Context.lean                  -- contextualize C(e⊳ctx) [done]; par_contextualize_ctx in Parallel [done] (scope dropped — copy is ξ-free)
  Parallel.lean                 -- Par/ParB, redMany_eq, devel, WF-scoped par_triangle, nf_iff [done; all 11 rules]
  Preservation.lean             -- WF.step / WF.par: reduction preserves WF          [done, M4.1]
  Diamond.lean                  -- ParWF + parWF_diamond/parWF_confluent             [done, M4.2a]
  Confluence.lean               -- confluence (WF-scoped headline; all 11 rules)     [done]
  Equivalence.lean              -- ≡ as an Equivalence on {e // WF e}              [done, M4 wrap]
  Canonical.lean                -- implicit parent ρ: canon + Canonical + step_canonical [done]
docs/  M0-spec.md (frozen contract), DESIGN.md (design + provenance)
scripts/  gen-rules.py, regen-rules.sh, difftest.sh, confluence-probe.sh
.github/
  actions/setup-lean/   composite action: cache + install Lean toolchain & mathlib
  workflows/            build.yml · rules-in-sync.yml · difftest.yml (one task each)
```

## Milestones

* **M0** — scaffold + frozen theorem statement + rule⇄constructor table + divergence
  note. **[done]**
* **M1** — terminating core: `Syntax`, decidable conditions, the `⊥`-collapse rules +
  congruence, the runnable demo, the phino differential harness, `reduce_sound`, and
  `local_confluence`. **[done]**
* **M2** — add `Rα` and the "`C` commutes with reduction" lemma.
* **M3** — parallel reduction `⇒` + complete development; the diamond. Switch off Newman.
  **[done]** — `Par`/`ParB`, `redMany_eq`, `devel`, the Takahashi triangle proved. (The M3
  capstone was an *unconditional* `step_confluent` for the then-`alpha`-free fragment; it was
  **retired at M4.2b** when `alpha` landed — unconditional confluence is false once `alpha` is
  present, so the headline became the `WF`-scoped `confluence` instead.)
* **M4** — the full calculus + the `WF`-scoped **Church–Rosser** headline; `≡` as an
  `Equivalence`. **[DONE — all 11 rules]** WF preservation; the WF-relativization bridge; the
  headline `confluence`; `alpha`; structural `nf`; `par_contextualize`; **`dot`** (`ρ`-feedback /
  non-terminating); **`copy`** (ξ-free local slot-fill — no `scope`). **`confluence` covers all
  eleven rules.** Wrap (polish, not the theorem): executable-reducer + `difftest` for all 11;
  `nf_iff`; `≡` as an `Equivalence`.

The project ends at M4: `confluence` covers the whole normalization relation `⟶`. The paper's
`λ`/`Δ` semantics (Morphing/Dataization) are separate, stateful relations — not part of `⟶`.

## Status

**M0–M4 done — the `WF`-scoped headline `confluence` is proved for all eleven rules (the full
φ-calculus).** Green, zero `sorry`/`axiom` (`#print axioms confluence` = `[propext, Quot.sound]`).
Highlights:

* **`Step`/`Par`** cover all eleven rules — the `⊥`-collapse six + `stay` + `phi` + `alpha` + `dot`
  + `copy` + full congruence closure.
* **M3:** `redMany_eq`, the complete development `devel`, and the Takahashi triangle.
* **M4.1:** `WF.step`/`WF.par` — reduction preserves well-formedness.
* **M4.2a:** the WF-relativization bridge (`ParWF`, `parWF_diamond`/`parWF_confluent`) and the
  permanent headline **`confluence`** (`WF e → e ↝∗ e₁ → e ↝∗ e₂ → ∃ e₃, …`).
* **M4.2b:** `alpha` + the now **`WF`-scoped** `par_triangle` (`lookup_alpha_absent_of_wf` is where
  `WF` becomes load-bearing); the unconditional `step_confluent`/`local_confluence` retired.
* **M4.3:** structural `nf` (`nf_par_eq`/`nf_devel`), `par_contextualize_ctx`, and **`dot`** — the
  `ρ`-feedback rule with the guard-on-developed-subterm `devel`.
* **M4.4:** **`copy`** — the ξ-free-guarded local slot-fill (`xiFree`, `fill`, `parB_fill`); under
  ξ-freeness the paper's `contextualize`/`scope` are **proved** the identity (`contextualize_eq_self`),
  so neither is modelled. `confluence` now covers **all eleven rules**.

The full-calculus diamond was de-risked beforehand (`docs/DESIGN.md` §7). **Wrap done** (polish,
not the headline): the executable reducer + `difftest` cover all 11 incl. `alpha` (17/17 vs phino);
`nf_iff` (`nf ↔ ¬Reducible`); `≡` as an `Equivalence`. See `docs/DESIGN.md`.

[paper]: https://github.com/objectionary/calculus-paper
[phino]: https://github.com/objectionary/phino
[oldproof]: https://github.com/objectionary/proof
