<!--
SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
SPDX-License-Identifier: MIT
-->

# M0 — Frozen specification

This is the contract the proof commits to. It is deliberately *narrower* than "the
paper's Fig. 4 verbatim"; the deviations are listed and justified below.

## The theorem

Let `⟶` be the single-step reduction relation: the **compatible (congruence)
closure** of the rule schemas below — every rule of phino 0.0.138 but `dotg` (#10) — over `Term` (formations `⟦B⟧`,
applications `e(τ↦e')`, dispatches `e.τ`, the locators `Φ`/`ξ`, and the terminator
`⊥`). Let `⟶∗` be its reflexive-transitive closure.

> **Confluence (Church–Rosser).** For all **well-formed** `e` (`WF e`) and all `e₁, e₂`:
> if `e ⟶∗ e₁` and `e ⟶∗ e₂`, then there exists `e₃` with `e₁ ⟶∗ e₃` and `e₂ ⟶∗ e₃`.

In Lean: a `WF`-relativized confluence, `WF e → e ⟶∗ e₁ → e ⟶∗ e₂ → ∃ e₃, …`
(`WF` is `PhiConfluence.WF` from `WellFormed.lean`: a formation's domain is duplicate-free
and free of positional `αᵢ` keys). It is proved by the diamond property of a
parallel-reduction relation `Par` (Takahashi complete development) transported via
`Relation.church_rosser`. The system is non-terminating, so this is **not** done with
Newman's lemma.

**Why `WF`-scoped (and not the unconditional `Confluent Step`).** `WF` has two clauses, and they
carry **different weight** — worth stating precisely:

* **`legalKey` (no positional `αᵢ` as a formation key) is *necessary for confluence*.** The
  counterexample that makes unconditional `Confluent Step` **false** once `alpha` is present is a
  `legalKey` violation: a *malformed* `⟦B₁, αᵢ↦e₁, B₂⟧(αᵢ↦e₂)` whose void slot sits at ordinal `i`
  lets `alpha` rename the argument (→ an object) while `over` fires (→ `⊥`), and object vs `⊥` never
  join (deviation #8). The diamond proof consumes exactly this clause (`lookup_alpha_absent_of_wf`,
  the `over` and `copy` cases of `par_triangle`). Faithful, too: phino's parser bars `αᵢ` formation keys.
* **`Nodup` (unique keys, Def. Binding 4.8) is a *faithfulness* clause, not a demonstrated
  confluence-necessity.** No duplicate-key non-joinable fork is known, and the diamond proof binds
  the `Nodup` field of `WF.form` but never uses it (only `legalKey`). `Nodup` is carried because it
  matches the paper's Def. Binding and makes our first-match `lookup` coincide with phino's matcher
  (deviation #6) — and because `WF.step`/`WF.par` preserve it. So "`WF` is necessary" is precise for
  `legalKey`; for `Nodup` it is faithfulness, not necessity.

So `WF`-scoping re-imposes exactly the paper's own grammar restrictions our looser `Binding` drops.
(Note the paper proves no confluence theorem at all; it *presupposes* confluence when defining `≡` as
"normal forms are syntactically identical". We prove it, `WF`-scoped because our encoding is looser
than the grammar.)

**phino's duplicate-`ρ` printer bug — resolved (phino #748).** Earlier, phino's *printer* injected a
duplicate void `ρ`, so `⟦ρ↦⟦⟧⟧` printed as `⟦ρ↦⟦ρ↦∅⟧, ρ↦∅⟧` (two `ρ` keys) — non-`Nodup`,
contradicting the Def. Binding its own parser enforces. Fixed in phino **#748** ("dont inject
duplicate void rho in salty printing"); phino now emits the single-`ρ` form our model already
produces (`canon ⟦ρ↦⟦⟧⟧ = ⟦ρ↦⟦ρ↦∅⟧⟧`). We never reproduced the bug (it would break `Nodup` and the
`lookup`-vs-matcher agreement), so model and phino now agree here.
(As of
M4.2b, `alpha` IS in `Step`, so `WF` is now load-bearing: the headline `confluence` carries
`WF e` and is proved via the WF-relativized diamond `ParWF a b := WF a ∧ Par a b`. The
earlier `alpha`-free fragment was unconditionally confluent; that unconditional
`step_confluent` was retired when `alpha` landed.)

## Rule ⇄ constructor table

Source of truth: the **paper** (reduction figure, `operators.tex`); `phino`'s
`resources/normalize/*.yaml` (`phino explain --normalize`) is the secondary interpretation that
renders into it. `nf e` means "`e` is in normal form" (no rule matches anywhere in
`e`); `C(·⊳·)` is contextualization (Fig. "Contextualization by induction"); `ordinal(B, i)` is the
key at position `i` of the *domain* of `B` (†).

| `phino` rule | Lean `Step` constructor | Pattern → result | Side condition |
|---|---|---|---|
| `dot`   | `Step.dot`   | `⟦B₁,τ↦e₁,B₂⟧.τ → C(e₁⊳⟦B₁,B₂,ρ↦∅⟧)(ρ↦⟦B₁,τ↦e₁,B₂⟧)` | `nf e₁` ∧ not both `λ∈B` and `Δ∈B` (`ρ↦∅` only when `B₁,B₂` lack `ρ`) |
| `dotg`  | — (#10)      | same, `(ρ↦Φ)` instead | the formation is the whole-program universe |
| `copy`  | `Step.copy`  | `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) → ⟦B₁,τ↦e₁,B₂⟧` | `ξFree e₁` ∧ `nf e₁` (phino's `𝑘` sigil; `scope`/`contextualize` vacuous — dev. #7) |
| `alpha` | `Step.alpha` | `⟦B⟧(αᵢ↦e) → ⟦B⟧(τ↦e)` | `τ = ordinal(B, i)` is void (†) |
| `overa` | `Step.overa` | `⟦B⟧(αᵢ↦e) → ⊥` | `ordinal(B, i)` is attached |
| `amiss` | `Step.amiss` | `⟦B⟧(αᵢ↦e) → ⊥` | `i ≥ |domain(B)|` |
| `stay`  | `Step.stay`  | `⟦B₁,ρ↦e₁,B₂⟧(ρ↦e₂) → ⟦B₁,ρ↦e₁,B₂⟧` | — |
| `over`  | `Step.over`  | `⟦B₁,τ↦e₁,B₂⟧(τ↦e₂) → ⊥` | `τ≠ρ` (attached slot) |
| `stop`  | `Step.stop`  | `⟦B⟧.τ → ⊥` | `τ∉B` ∧ `φ∉B` ∧ `λ∉B` |
| `null`  | `Step.null`  | `⟦B₁,τ↦∅,B₂⟧.τ → ⊥` | — (void slot) |
| `miss`  | `Step.miss`  | `⟦B⟧(τ↦e) → ⊥` | `τ∉B` ∧ `τ` not positional `αᵢ` |
| `dl`    | `Step.dl`    | `⟦B⟧ → ⊥` | `λ∈B` ∧ `Δ∈B` |
| `dd`    | `Step.dd`    | `⊥.τ → ⊥` | — |
| `dc`, `dca` | `Step.dc` | `⊥(τ↦e) → ⊥`, `⊥(αᵢ↦e) → ⊥` | — (one Lean rule covers both sorts) |

(†) **Positional rules count the *domain*.** phino's `domain` excludes the `Δ`/`λ` assets
(phino #749) and the parent `ρ` too, so `ordinal bs i` (`Attributes.lean`) skips
both: in `⟦λ⤍Fn, x↦∅, ρ↦∅⟧` the ordinal of `x` is `0` and there is no ordinal `1`. This is the
paper's Def. Ordinal / Def. Domain. The three positional rules partition every ordinal, so a
positional application on a formation always has a redex.

Plus the four congruence constructors `Step.congDispatch`, `Step.congAppFn`,
`Step.congAppArg`, `Step.congForm` — covering every recursive `Term` position (dispatch
subject, application subject, application argument, and a formation binding's value),
so reduction may occur *anywhere*, matching the paper (`operators.tex`: "rules may be
applied in any order"). `Step.congForm` uses the paper's `⟦B₁,τ↦e,B₂⟧` splitting.

Disjointness (the root rules are mutually exclusive on a given redex, with the noted
exceptions):

* dispatch `⟦B⟧.τ` is split by `dot` (τ attached) / `null` (τ void) / `stop` (τ absent,
  φ,λ absent); `⊥.τ` is `dd`. A dispatch of an absent `τ` on a formation holding `φ` or `λ` is
  normal (phino dropped its `phi` rule), as are terms like `Φ.τ` and `ξ.τ` — this is a partition
  of *reducible* dispatch redexes, not of all terms.
* application `⟦B⟧(τ↦e)` by a non-positional `τ` is split by `stay` (τ=ρ attached) / `over` (τ≠ρ
  attached) / `copy` (τ void, argument `ξ`-free and normal) / `miss` (τ absent); by a positional
  `αᵢ` it is split by `alpha` / `overa` / `amiss` on `ordinal(B, i)`; `⊥(…)` is `dc`.
* **Exception:** `dl` overlaps every rule on a formation holding both `λ` and `Δ`. Each such fork
  joins at `⊥`, except `dot`, which would carry the formation into `ρ` and leave a stuck
  `…(ρ↦⊥)`; phino 0.0.138 therefore guards `dot` against it (phino #1395), and so does `Step.dot`.

## How our model relates to the paper

We match the **current** paper, whose Fig. 4 is generated from current phino
(`phino explain --normalize`). The items below record (a) where *older/published*
forms differed, (b) scoping choices for the confluence theorem, and (c) standing
assumptions — not gaps against the current paper.

1. **`over` requires an *attached* `τ`.** The current Fig. 4 (generated from phino)
   and our `over` both use the disjoint attached-slot form `⟦B₁,τ↦e₁,B₂⟧(τ↦e₂)`. A
   *naive* reading of the membership predicate `τ∈b` (defined in Def. 4.9, Formation —
   it holds for void keys too) would license a looser `over` overlapping `copy` on a
   void slot (object vs `⊥`, which never join); the published arXiv v9 PDF, built with
   an older phino, rendered exactly that looser form. We follow the current, disjoint
   form. (Worth keeping the `∈`-based prose from suggesting the loose reading.)
2. **`dot`/`copy` are `nf`-guarded.** They fire only when the relevant
   sub-expression is already normal. This forces an inner-first order, makes each rule
   single-path, and removes the `dot`↔`copy` ordering ambiguity. It also makes `⟶` a
   *conditional* relation with non-monotone guards — the main proof subtlety.
3. **Small-step `copy` (not big-step).** The current paper's `copy` (generated from
   phino) is already the small-step `nf`-guarded form we use. Older/published forms
   (arXiv v9) had a big-step `Rcopy` that normalizes its argument to `n` inside the
   rule (`C(e⊳eς) ⟶∗ n`), presupposing uniqueness of normal forms (= confluence). We
   follow the current small-step form, avoiding the circularity; against the current
   paper there is nothing to reconcile, and the superseded big-step form is not modelled.
4. **`λ`/`Δ` atoms are outside the normalization relation `⟶`.** Only `dl` looks at them, and
   only to collapse a formation holding both to `⊥`. Their reduction is the paper's
   *separate* **Morphing** (`fig:morphing` — `Mlambda` calls a host atom `f` by value) and
   **Dataization** (`fig:dataization`) partial functions: stateful, side-effecting,
   host-dependent — *functions*, not a term-rewriting relation (so the relevant property
   there is determinism, not confluence). Confluence of `⟶` therefore neither needs nor
   includes them; `λ`/`Δ` are represented as **inert atoms** (`Binding.lambda`/
   `Binding.delta`) that never fire. This is a permanent scope boundary set by the paper's
   own structure (normalization vs. morphing/dataization are separate sections), not
   unfinished work.
5. **`ρ`-feedback (landed).** `dot`'s `ρ`-introduction (which makes the system non-terminating)
   landed in `Step`/`Par` at **M4.3** with the `nf`-guard and `contextualize` (receiver = the
   dispatched formation, so no `scope`). `copy` landed at **M4.4** (see #7). `alpha` landed at
   **M4.2b** (positional; now modelled by `ordinal` — the domain ordinal, assets and `ρ` skipped,
   matching the paper and phino — see note †). Issue #73 brought `Step` to phino 0.0.138:
   `phi` is gone, `overa`, `amiss` and `dl` are new, `dot` contextualizes against `⟦B₁, B₂⟧`, and
   `copy` accepts `⊥`. So **every rule `phino rewrite` applies is in `Step`/`Par`**, and
   `confluence` covers them. (Earlier drafts said "M1–M2 use a
   simplified `dot`" — there was never a simplified `dot`; it arrived at M4.3 with full ρ-feedback.)
6. **Unique-key well-formedness (Def. 4.8).** Formations are assumed to have unique
   attribute keys; under that invariant our first-match `lookup` coincides with phino's
   any-position match. Documented in `Attributes.lean`; to be carried as a hypothesis /
   indexed type once formation-rebuilding rules arrive. (This is deviation #6 above; the
   design rationale is in `docs/DESIGN.md` §4/§6.)
7. **`copy`'s guards are `ξFree e₁` ∧ `nf e₁` — we KEEP phino's `ξ`-free (this REVERSES the
   earlier draft of this note, settled at M4.4 by the author).** `Step.copy` (`Step.lean`) is the
   local slot-fill `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) → ⟦B₁,τ↦e₁,B₂⟧` guarded by `ξFree e₁` then `nf e₁` — **no
   `scope`, no `contextualize`.** Rationale: phino's printed figure renders `copy` with `nf(e₁)`
   only (its renderer strips the `ξ` condition), *but phino's engine enforces `ξ`-free*; and under
   `ξ`-freeness, `contextualize(e₁, scope) = e₁` is **proved** (`contextualize_eq_self`,
   `Parallel.lean`, `[propext]`), so the figure's `scope`/`contextualize` are operationally vacuous and dropping
   them is exact, not a weakening. Keeping `ξ`-free also (a) keeps `copy` a *local* rule needing no
   context-dependent `scope`, (b) puts `copy` inside the de-risked/fuzzed fragment (the de-risk
   assumed `ξ`-freeness), and (c) makes `difftest` valid (the `ξ`-dropped `copy` diverges on
   `⟦x↦∅⟧(x↦ξ)` via `scope` re-injection). The author is correcting the paper figure + phino to this
   form, so this is a 1:1 match, not a deviation. The single `nf` is `ξFree`-aware in its
   void-application case (it is *not* a `copy`-specific `nf` — it is the one `nf` encoding `copy`'s
   guard, exactly as phino's one `isNF` does).
8. **Formation keys are non-positional attributes only.** The paper grammar
   (`syntax.tex`) puts positional `αᵢ` solely in application-argument pairs; a formation
   binding's key is an `Attribute` ∈ {`φ`, `ρ`, label}. Our `Binding` accepts any `Attr`
   (including `Attr.alpha`), so a malformed formation with an `αᵢ` key is representable.
   Harmless in the `⊥`-fragment (no rule builds one; `lookup` is key-agnostic); to be
   enforced as a well-formedness side-condition alongside the unique-key invariant when
   `alpha`/`copy`/`dot` arrive.
9. **Every formation carries an implicit parent `ρ` (modelled, not a deviation).** The paper
   (`foundations.tex`, Def. Parent) and phino give every formation a parent `ρ`, void until set —
   the paper *grammar* does not mandate it, so it is supplied semantically (phino appends `ρ↦∅`
   where absent, recursively). We model this with `canon` (`Canonical.lean`), which injects `ρ`
   exactly as phino does; `canon_canonical`/`wf_canon`/`step_canonical` prove it is established,
   `WF`-preserving, and closed under reduction. Canonical terms are `WF`, so the headline governs
   them — the result is confluence of phino's *actual* calculus, `ρ` included (not a `ρ`-free
   fragment). `difftest` confirms the match on real formation results. Full account: `DESIGN.md` §9.
10. **`dotg` is not modelled (universe-free).** phino's `dotg` fires instead of `dot` when the
    dispatched formation is the whole program (`e-match` against the universe), and then puts `Φ`
    in the result's `ρ`. `Step` models `phino rewrite` on a bare expression, where no formation is
    the universe, so `dot` always fires and `dotg` never does.
