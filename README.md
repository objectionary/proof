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
reference manipulator [`phino`][phino] — the same rules the [paper][paper]'s Fig. 4 is
generated from — and supersedes the earlier minimal/extended development kept in this repository's
history (which finished only the minimal calculus).

**`#print axioms PhiConfluence.confluence` = `[propext, Quot.sound]`** — no `sorry`, no
`Classical.choice`.

## The theorem

`⟶` is the compatible (congruence) closure of the `phino` 0.0.138 rules
(`dd, dc, dca, null, over, stop, miss, stay, alpha, overa, amiss, dot, copy, dl`) over `Term`
(formations `⟦B⟧`, applications `e(τ↦e')`, dispatches `e.τ`, the locators `Φ`/`ξ`, and the
terminator `⊥`). The fifteenth rule, `dotg`, fires only on the whole-program universe, which
`phino rewrite` never sees, so it is not modelled. `⟶∗` is the reflexive-transitive closure.
`PhiConfluence.confluence`:

> For all **well-formed** `e`, if `e ⟶∗ e₁` and `e ⟶∗ e₂`, then there exists `e₃` with `e₁ ⟶∗ e₃`
> and `e₂ ⟶∗ e₃`.

`WF` is `PhiConfluence.WF` from `WellFormed.lean`: a formation's domain is duplicate-free and free
of positional `αᵢ` keys. The theorem is proved via **parallel reduction** and the **Takahashi
diamond** (mathlib's `Relation.church_rosser`); the system is non-terminating (`⟦x↦y,y↦x⟧.x`
diverges), so Newman's lemma does not apply.

The contract is deliberately *narrower* than "the paper's Fig. 4 verbatim"; the deviations are
listed and justified [below](#how-the-model-relates-to-the-paper). The paper itself proves no
confluence theorem: it *presupposes* confluence when it defines `≡` as "normal forms are
syntactically identical".

### Why `WF`-scoped

`WF` re-imposes exactly the paper's own grammar restrictions that the deliberately looser
`Binding` encoding drops. Its two clauses carry **different weight**:

* **`legalKey` (no positional `αᵢ` as a formation key) is *necessary for confluence*.** The
  counterexample that makes unconditional `Confluent Step` **false** once `alpha` is present is a
  `legalKey` violation: a *malformed* `⟦B₁, αᵢ↦e₁, B₂⟧(αᵢ↦e₂)` whose void slot sits at ordinal `i`
  lets `alpha` rename the argument (→ an object) while `over` fires (→ `⊥`), and object vs `⊥` never
  join (deviation 8). The diamond proof consumes exactly this clause (`lookup_alpha_absent_of_wf`,
  the `over` and `copy` cases of `par_triangle`). It is faithful, too: phino's parser bars `αᵢ`
  formation keys.
* **`Nodup` (unique keys, Def. Binding 4.8) is a *faithfulness* clause, not a demonstrated
  confluence-necessity.** No duplicate-key non-joinable fork is known, and the diamond proof binds
  the `Nodup` field of `WF.form` but never uses it. `Nodup` is carried because it matches the
  paper's Def. Binding and makes our first-match `lookup` coincide with phino's matcher
  (deviation 6), and because `WF.step`/`WF.par` preserve it.

phino once printed a non-`Nodup` term: `⟦ρ↦⟦⟧⟧` came out as `⟦ρ↦⟦ρ↦∅⟧, ρ↦∅⟧`, with two `ρ` keys.
That printer bug, contradicting the Def. Binding its own parser enforces, was fixed in phino
**#748**. Our model never reproduced it and already gave `canon ⟦ρ↦⟦⟧⟧ = ⟦ρ↦⟦ρ↦∅⟧⟧`, so model and
phino now agree.

## Verify it yourself

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh   # one-time: Lean's toolchain manager
pip install -r .github/requirements.txt                  # one-time: Python deps of the generators
make                        # green ⇒ every theorem is kernel-checked and axiom-clean, as in CI
lake exe demo               # the rules + example reductions, by the project's own reducer
make difftest               # our reducer vs `phino rewrite --normalize` (needs phino on PATH)
```

`make` needs GNU Make 4.3 or newer. It fetches mathlib's prebuilt artifacts, generates the rule
files from pinned phino (and regenerates them only when `.phino-version` or a generator changes),
runs the generator unit tests and `lake build`, and checks that no headline theorem depends on a
forbidden axiom.

The rule files (`Rules.lean`, `RuleData.lean`) are not kept in Git: they are generated from the
`resources/normalize/*.yaml` of the phino pinned in `.phino-version` — the same source the paper's
Fig. 4 renders from — so they cannot drift from phino. `reduce_sound` certifies that every step the
runnable reducer takes is a genuine `Step`, and `difftest` confirms our reducer's normal forms
match phino's. Run `#print axioms <name>` on any result to inspect its axiom footprint.

The demo, `lake exe demo`, prints the normalization rules in the paper's Unicode notation and
reduction traces of example φ-programs computed by our own `reduceStep`.

## The rules

Source of truth: the **paper** (reduction figure, `operators.tex`); `phino`'s
`resources/normalize/*.yaml` (`phino explain --normalize`) is the secondary interpretation that
renders into it. `nf e` means "`e` is in normal form" (no rule matches anywhere in `e`); `C(·⊳·)`
is contextualization (Fig. "Contextualization by induction"); `ordinal(B, i)` is the key at
position `i` of the *domain* of `B` (†).

| `phino` rule | Lean `Step` constructor | Pattern → result | Side condition |
|---|---|---|---|
| `dot`   | `Step.dot`   | `⟦B₁,τ↦e₁,B₂⟧.τ → C(e₁⊳⟦B₁,B₂,ρ↦∅⟧)(ρ↦⟦B₁,τ↦e₁,B₂⟧)` | `nf e₁` ∧ not both `λ∈B` and `Δ∈B` (`ρ↦∅` only when `B₁,B₂` lack `ρ`) |
| `dotg`  | — (dev. 10)  | same, `(ρ↦Φ)` instead | the formation is the whole-program universe |
| `copy`  | `Step.copy`  | `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) → ⟦B₁,τ↦e₁,B₂⟧` | `ξFree e₁` ∧ `nf e₁` (phino's `𝑘` sigil; `scope`/`contextualize` vacuous — dev. 7) |
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
(phino #749) and the parent `ρ` too, so `ordinal bs i` (`Attributes.lean`) skips both: in
`⟦λ⤍Fn, x↦∅, ρ↦∅⟧` the ordinal of `x` is `0` and there is no ordinal `1`. This is the paper's
Def. Ordinal / Def. Domain. The three positional rules partition every ordinal, so a positional
application on a formation always has a redex.

Plus the four congruence constructors `Step.congDispatch`, `Step.congAppFn`, `Step.congAppArg`,
`Step.congForm` — covering every recursive `Term` position (dispatch subject, application subject,
application argument, and a formation binding's value), so reduction may occur *anywhere*,
matching the paper (`operators.tex`: "rules may be applied in any order"). `Step.congForm` uses
the paper's `⟦B₁,τ↦e,B₂⟧` splitting.

The root rules are mutually exclusive on a given redex, with the noted exception:

* dispatch `⟦B⟧.τ` is split by `dot` (τ attached) / `null` (τ void) / `stop` (τ absent, φ,λ
  absent); `⊥.τ` is `dd`. A dispatch of an absent `τ` on a formation holding `φ` or `λ` is normal
  (phino dropped its `phi` rule), as are terms like `Φ.τ` and `ξ.τ` — this is a partition of
  *reducible* dispatch redexes, not of all terms.
* application `⟦B⟧(τ↦e)` by a non-positional `τ` is split by `stay` (τ=ρ attached) / `over` (τ≠ρ
  attached) / `copy` (τ void, argument `ξ`-free and normal) / `miss` (τ absent); by a positional
  `αᵢ` it is split by `alpha` / `overa` / `amiss` on `ordinal(B, i)`; `⊥(…)` is `dc`.
* **Exception:** `dl` overlaps every rule on a formation holding both `λ` and `Δ`. Each such fork
  joins at `⊥`, except `dot`, which would carry the formation into `ρ` and leave a stuck
  `…(ρ↦⊥)`; phino 0.0.138 therefore guards `dot` against it (phino #1395), and so does `Step.dot`.

## How the model relates to the paper

We match the **current** paper, whose Fig. 4 is generated from current phino
(`phino explain --normalize`). The items below record (a) where *older/published* forms differed,
(b) scoping choices for the confluence theorem, and (c) standing assumptions — not gaps against
the current paper.

1. **`over` requires an *attached* `τ`.** The current Fig. 4 and our `over` both use the disjoint
   attached-slot form `⟦B₁,τ↦e₁,B₂⟧(τ↦e₂)`. A *naive* reading of the membership predicate `τ∈b`
   (defined in Def. 4.9, Formation — it holds for void keys too) would license a looser `over`
   overlapping `copy` on a void slot (object vs `⊥`, which never join); the published arXiv v9
   PDF, built with an older phino, rendered exactly that looser form. We follow the current,
   disjoint form.
2. **`dot`/`copy` are `nf`-guarded.** They fire only when the relevant sub-expression is already
   normal. This forces an inner-first order, makes each rule single-path, and removes the
   `dot`↔`copy` ordering ambiguity that blocked the old proof. It also makes `⟶` a *conditional*
   relation with non-monotone guards — the main proof subtlety.
3. **Small-step `copy` (not big-step).** The current paper's `copy` is already the small-step
   `nf`-guarded form we use. Older forms (arXiv v9) had a big-step `Rcopy` that normalizes its
   argument to `n` inside the rule (`C(e⊳eς) ⟶∗ n`), presupposing uniqueness of normal forms (=
   confluence). We follow the current form, avoiding the circularity; the superseded big-step form
   is not modelled.
4. **`λ`/`Δ` atoms are outside `⟶`.** Only `dl` looks at them, to collapse a formation holding
   both to `⊥`. Their reduction is the paper's *separate* **Morphing** (`fig:morphing` — `Mlambda`
   calls a host atom `f` by value) and **Dataization** (`fig:dataization`) partial functions:
   stateful, side-effecting, host-dependent — *functions*, not a term-rewriting relation, so the
   relevant property there is determinism, not confluence. `λ`/`Δ` are represented as **inert
   atoms** (`Binding.lambda`/`Binding.delta`) that never fire. This is a permanent scope boundary
   set by the paper's own structure, not unfinished work, and it is why the paper's Appendix-A
   examples are validated through `difftest` (against a merged `runtime.phi`) rather than
   re-encoded in Lean.
5. **Every rule `phino rewrite` applies is in `Step`/`Par`.** `dot`'s `ρ`-introduction (which
   makes the system non-terminating) landed with the `nf`-guard and `contextualize` (receiver = the
   dispatched formation, so no `scope`); `copy` and the positional `alpha` followed. Issue #73
   brought `Step` to phino 0.0.138: `phi` is gone, `overa`, `amiss` and `dl` are new, `dot`
   contextualizes against `⟦B₁, B₂⟧`, and `copy` accepts `⊥`.
6. **Unique-key well-formedness (Def. 4.8).** Formations are assumed to have unique attribute
   keys; under that invariant our first-match `lookup` coincides with phino's any-position match.
   It is carried as the `Nodup` clause of `WF`.
7. **`copy`'s guards are `ξFree e₁` ∧ `nf e₁`.** `Step.copy` is the local slot-fill
   `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) → ⟦B₁,τ↦e₁,B₂⟧` — **no `scope`, no `contextualize`.** phino's printed figure
   renders `copy` with `nf(e₁)` only (its renderer strips the `ξ` condition), *but phino's engine
   enforces `ξ`-freeness*; and under `ξ`-freeness, `contextualize(e₁, scope) = e₁` is **proved**
   (`contextualize_eq_self`, `Parallel.lean`, `[propext]`), so the figure's `scope`/`contextualize`
   are operationally vacuous and dropping them is exact, not a weakening. Keeping `ξ`-freeness
   also (a) keeps `copy` a *local* rule needing no context-dependent `scope`, (b) puts `copy`
   inside the de-risked fragment, and (c) makes `difftest` valid (the `ξ`-dropped `copy` diverges
   on `⟦x↦∅⟧(x↦ξ)` via `scope` re-injection). The author is correcting the paper figure and phino
   to this form, so this is a 1:1 match. The single `nf` is `ξFree`-aware in its void-application
   case, exactly as phino's one `isNF` is.
8. **Formation keys are non-positional attributes only.** The paper grammar (`syntax.tex`) puts
   positional `αᵢ` solely in application-argument pairs; a formation binding's key is an
   `Attribute` ∈ {`φ`, `ρ`, label}. Our `Binding` accepts any `Attr` (including `Attr.alpha`), so
   a malformed formation with an `αᵢ` key is representable; the `legalKey` clause of `WF` excludes
   it.
9. **Every formation carries an implicit parent `ρ`.** This is modelled, not a deviation — see
   [The implicit parent](#the-implicit-parent-ρ).
10. **`dotg` is not modelled.** phino's `dotg` fires instead of `dot` when the dispatched
    formation is the whole program (`e-match` against the universe), and then puts `Φ` in the
    result's `ρ`. `Step` models `phino rewrite` on a bare expression, where no formation is the
    universe, so `dot` always fires and `dotg` never does.

A further, intentional looseness of the encoding: `Step.alpha`/`Step.copy` carry no per-rule
`Nodup`/`legalKey` premise at the constructor, relying on the headline's `WF` to exclude malformed
redexes globally (matching phino, which checks no such premise). Likewise `WF`'s `Nodup` is over
`domain` (assets excluded), so it does not forbid duplicate `λ`/`Δ` assets — fine while assets are
inert, a latent looseness to tighten only if asset reduction is modelled.

## The implicit parent (`ρ`)

The paper (`foundations.tex`, Def. Parent) and phino treat **every formation as carrying a parent
`ρ`, void until set** (a `this`-pointer, void until a method is called). The paper *grammar*
(`syntax.tex`) does **not** mandate `ρ` — a formation may be written `⟦⟧` — so the parent is
supplied **semantically**: phino appends a `ρ↦∅` **at the end** of every formation that lacks one
(`⟦x↦Φ⟧` ⟶ `⟦x↦Φ, ρ↦∅⟧`, recursively; an explicit `ρ` is kept in place, never duplicated).
Omitting it would diverge from phino *and* the paper three ways: rule choice (`⟦⟧(ρ↦Φ)` is
`copy→⟦ρ↦Φ⟧` for phino but `miss→⊥` without `ρ`), `alpha` indexing (its positional index counts
the trailing `ρ`: `⟦x↦∅⟧(~1↦Φ) ⟶ ⟦x↦∅, ρ↦Φ⟧`), and normal-form shape (every formation NF carries
`ρ↦∅`).

We model it as a canonicalisation in `Canonical.lean`:

* `canon` / `canonB` — the injection: recursively append `ρ↦∅` to every `ρ`-less formation
  (explicit `ρ` kept in place), exactly phino's behaviour.
* `Canonical` / `CanonicalB` — the invariant "every formation carries a `ρ`".
* `canon_canonical` (`[propext]`) — `canon` always establishes it; `wf_canon`
  (`[propext, Quot.sound]`) — `canon` preserves `WF` (it adds `ρ` only when absent, so no duplicate
  key, and `ρ` is legal); **`step_canonical`** (`[propext]`) — **reduction preserves
  `Canonical`**, so phino's parent-everywhere term space is *closed* under our `Step`.

Because canonical terms are `WF`, the headline `confluence` already governs them, so the result is
confluence of **phino's actual calculus**, not a `ρ`-free fragment. This was never a threat to
confluence (the implicit `ρ` is a representational default, not a rule; routing `ρ`-application to
`copy` removes the `miss`-on-`ρ` case and adds no critical pair) — it was a term-level *fidelity*
obligation, discharged both formally (the three lemmas) and behaviourally (`difftest`, including
the cases that diverged before `canon`: `⟦⟧(ρ↦Φ)` and bare value formations).

## Design decisions

The artifacts relate as follows. The paper ([`objectionary/calculus-paper`][paper]) is the
informal spec; **its Fig. 4 rules and Appendix-A example reductions are auto-generated by
`phino`** (`\iexec{phino explain --normalize}`, `phino rewrite`), checked in its CI.
[`phino`][phino] is the **authoritative, executable** rule spec, in `resources/normalize/*.yaml`.
The retired Minimal/Extended development in this repository's history was reused only as a
**technique template** (the Takahashi parallel-reduction skeleton and the `Record` design). Because
the paper's rules and examples are generated *from phino*, "match the paper" reduces to "match
phino", which is executable and testable. Two phino bugs surfaced and were fixed during this work,
the `alpha`-ordinal asset counting (phino #749) and the duplicate-`ρ` printer (phino #748); our
model already matched the paper-faithful side of both.

| Decision | Rationale |
|---|---|
| **Source of truth = phino + calculus-paper LaTeX source** (never the arXiv PDF) | The PDF is a stale build; the repo source regenerates rules from current phino. Paper-first, phino as its executable interpretation. |
| **Prove via parallel reduction → diamond → `Relation.church_rosser`** | The system is **non-terminating**, so Newman's lemma is unavailable. The Tait–Martin-Löf/Takahashi method needs no termination. |
| **Build on mathlib's `Prop`-valued `Relation` API** | Idiomatic, least code; `church_rosser` already proves "diamond ⇒ confluent-closure". |
| **Named attributes** (`φ, ρ, αᵢ, label`) | Matches the paper and phino; makes contextualization `C` and the `αᵢ` ordinals natural. (De Bruijn would obscure named-attribute semantics.) |
| **`nf` defined structurally** (like phino's `isNF`), not as "no `Step`" | Avoids an import cycle and the big-step circularity; a *local* property, well-defined regardless of confluence. A single `nf` encodes every rule's redex, including `copy`'s `ξ`-free guard in its void-application case. |
| **Executable `reduceStep` separate from relational `Step`, linked by `reduce_sound`** | Lets the demo *run* and print traces, while a proof certifies the printed steps are genuine `Step`s — a tighter link than phino has (its Haskell engine is not proven against its YAML). |
| **`copy` is `ξ`-free and local** (no `scope`/`contextualize`) | Dropping `scope`/`contextualize` is exact, not a weakening, and keeps `copy` inside the de-risked fragment (deviation 7). |
| **Headline is `WF`-scoped** | `legalKey` is necessary for confluence; `Nodup` is faithfulness. Both re-impose the paper's own grammar (see [Why `WF`-scoped](#why-wf-scoped)). |

## Proof strategy

1. Define single-step `Step` (`⟶`): phino's rules + the four congruences, phino-faithful.
2. Define **parallel reduction** `Par` (contracts any set of redexes at once; congruence built in)
   and a total **complete development** `devel`.
3. Prove `Step ⊆ Par ⊆ Step∗`, so `ReflTransGen Step = ReflTransGen Par` (`redMany_eq`).
4. Prove the **Takahashi triangle** `WF e → Par e u → Par u (devel e)`, giving the diamond.
5. `Abstract.Diamond.confluent` (via `church_rosser`) turns the diamond into confluence; transport
   to `Step` (the closures coincide).
6. Define `≡` as convertibility; confluence makes it an `Equivalence` on `{e // WF e}`.

The hardest parts, all discharged: the **"`C` commutes with reduction"** lemma
(`par_contextualize_ctx`), the **non-monotone `nf` guards** threaded through parallel reduction,
and the **`ρ`-feedback** of `dot` (the source of non-termination).

Three structural decisions carry the diamond layer; each load-bearing shape was validated
`[propext]`-clean against Lean `v4.30.0` + mathlib.

1. **Well-formedness as a `Prop` predicate.** Mutual `WF`/`WFB` (`WellFormed.lean`, importing only
   `Syntax`) is carried as a *hypothesis* on the diamond and the headline — **not** an indexed
   `Binding` type (which would force re-deriving `Syntax`/`Step`/`Attributes`). Its preservation
   engine (`domain_append`/`domain_set`, mirroring `lookup_set_*`) rests on a single fact: reducing
   a binding's *value* never changes the `domain`, so `WF` survives reduction (`WF.step`/`WF.par`,
   `Preservation.lean`).
2. **Parallel reduction `Par`** = mutual `Par`/`ParB` with a **bespoke cons-structured `ParB`**
   (the `List.Forall₂ ParBind` route is kernel-rejected as a nested inductive carrying `Par`). The
   append-index lives only on `Step.congForm`, crossed once by `parB_set`. Mutual induction goes
   through `induction h using Par.rec (motive_2 := …)` with `motive_1` inferred. The cons-lift
   `redMany_form_cons` is proved by `induction … generalizing` + `form_step_inv` (*not*
   `ReflTransGen.lift` — unsound, because `stay` turns app→form).
3. **The Takahashi guard-on-developed-subterm variant** (this, *not* Huet single-step on `Step`).
   `dot`'s result places the developed formation `⟦bs'⟧` in *both* the `contextualize` receiver
   and the `ρ`-argument, so reduction is **duplicating** and a `dot`-vs-sibling fork needs more
   than one step on both sides, breaking Huet. One `Par` step contracts all copies at once, so the
   triangle needs no non-duplication argument. The parallel-step constructors check `nf` on the
   *developed* child `e₁'`, not the original `e₁` (e.g. `Par.dot` reads the guard off `develB bs`
   via `lookup`, keeping `devel` structural) — this restores a total `devel` and the triangle.

**WF-relativization.** `church_rosser` / `Abstract.Diamond.confluent` demand an *unconditional*
strip `∀ a b c, r a b → r a c → ∃ d, …`. A `WF`-hypothesised strip does not discharge it for the
full calculus (off-`WF`, the `alpha`-vs-`over` diamond genuinely fails). The fix: relativize to
`ParWF a b := WF a ∧ Par a b`, prove `WF.par` (so `ParWF` stays `WF`-rooted), whence the strip for
`ParWF` holds *unconditionally* (it is vacuous when `¬WF a`); feed that to the generic diamond to
get `Confluent (ReflTransGen ParWF)`, then bridge back to `WF`-rooted `ReflTransGen Step` via
`redMany_eq`. `Diamond ParWF` needs `WF` of the *source* only, so no new `Abstract` lemma is
required (`Diamond.lean`).

Before investing in the Lean diamond, the central open question — *does the full calculus even
have the diamond, given the non-monotone `nf` guards?* — was stressed empirically and by
structural analysis. The empirical probe was a **fixed corpus of 7 hand-crafted programs plus the
paper's Appendix-A examples**, each run under rule-order `--shuffle` and an off-strategy
single-rule redex-position check; no divergence was found. The analysis concluded confluence
holds, for reasons the mechanized proof then made rigorous:

* **No genuine root critical pairs.** The two LHS-overlap groups are mutually exclusive by guards
  along root-stable axes — dispatch `⟦B⟧.τ` {dot, null, stop, dd} by slot state
  (attached/void/absent) × `φ`-membership × subject head; formation application `⟦B⟧(τ↦e)` {copy,
  alpha, overa, amiss, over, stay, miss, dc} by slot state × name kind (positional `αᵢ` →
  alpha/overa/amiss by the state at its domain ordinal, named → copy/over/miss, `ρ` → stay) ×
  subject head. The one overlap added since, `dl`, joins at `⊥` because `dot` is guarded (phino
  #1395). This rests on three facts: duplicate keys are barred (a slot is in exactly one state),
  `α`-names cannot be formation slots, and `index()` is defined only for `αᵢ` — exactly the `WF`
  invariants.
* **All non-root critical pairs join.** The *duplication* diamond (`dot` relocates and
  contextualizes a redex-bearing sibling into the `ρ`-context — reducing before or after gives the
  identical normal form) and the *discard* diamond (over/null/stop/miss/dc/dd erase to the
  absorbing `⊥` regardless of inner activity — which is why they need no `nf` guard, and why
  Church–Rosser holds *despite* non-termination).
* **The non-monotone guard is real but benign.** Reducing inside `e₁` can expose a fresh outer
  `dot`/`copy` redex, so the *naive* maximal development and one-step triangle break. But the
  non-monotonicity *serializes* (no competing root redex exists while `¬nf(e₁)`) and is monotone
  in the *destruction* direction (no present guarded redex is destroyed by a sibling contraction)
  — which is precisely what the guard-on-developed-subterm variant exploits.

Routes considered and rejected: Huet single-step strong confluence (broken by `dot`'s
duplication), orthogonality (non-left-linear LHS repeat `τ`), Hindley–Rosen (no mathlib
commutation API), decreasing diagrams (no Lean port, unneeded).

## Faithfulness

Lean's kernel guarantees **soundness** (the proof establishes the statement). It does *not*
guarantee **adequacy** (the statement and definitions capture φ-calculus) — that gap is
irreducible when one side is an informal paper. It is shrunk and cross-checked from several
independent directions:

* **Tiny, human-readable trusted surface.** Only `Syntax`, `Step`, `⟶∗`, and the `confluence`
  statement must be read and endorsed — a few dozen lines.
* **Rule transcription vs phino.** The fifteen-rule *display* table (`Rules.lean`) is
  **generated** from pinned phino before every build, so it cannot drift from phino. The *proof
  relation* `Step` is hand-written (constructors are needed for case analysis) and pinned to phino
  **behaviorally** by `difftest`.
* **Differential testing against phino.** `Difftest.lean` + `.github/difftest.sh` normalize each
  program with both `phino rewrite --normalize` and our reducer and assert equality — **26/26**,
  exercising every modelled rule (including the positional rules' domain-ordinal skip of `Δ`/`λ`
  assets and `ρ`) on `⊥`-collapse *and* real formation results. This is the same `phino rewrite`
  mechanism the paper's Appendix A is generated from, so it doubles as reproducing the paper's
  examples (the subset that needs no `λ`/`Δ` dataization).
* **`#print axioms` CI gate.** The headline results (`confluence`, `conv_equivalence`,
  `reduce_sound`, `par_triangle`, `parWF_diamond`, `nf_iff`) are gated to depend only on
  `propext`/`Quot.sound` — never `sorryAx`, `Classical.choice`, or `native_decide`.

Every arrow in the faithfulness loop is CI-checked or kernel-proved:

```
   paper ──(phino explain/rewrite, calculus-paper CI)──▶ phino rules + example reductions
     ▲                                                          │
     │                                              (CI diff, this project)
     │                                                          ▼
     └──────────────────────────────────  our printed rules + our reductions (the demo)
                                                                │
                                                (Lean: reduce_sound, reduceStep ⊆ Step)
                                                                ▼
                                                          relation  Step
                                                                │
                                                  (Lean kernel: no sorry/axiom)
                                                                ▼
                                                       confluence theorem
```

The trusted computing base is exactly: (a) Lean's kernel; (b) the definitions and the theorem
statement; (c) for the demo and CI, the term printer/parser bridge and phino. The proof adds
nothing to (a)–(c).

A gold-standard, optional improvement would generate the Lean `Step` *relation* (not just the
display table) from phino's YAML, so the proof object and the paper's figure share a single
source. Today `Step` is hand-written and pinned to phino behaviorally by `difftest`; generating it
would make the pin structural. It does not affect the proof's validity.

## How it fits together

```
Main.lean / Difftest.lean         demo + phino differential test
PhiConfluence/
  Syntax · Attributes · WellFormed  Term/Binding/Attr; lookup/fill/ordinal/erase; the WF predicate
  Step                              the relation ⟶ — phino's rules + congruence closure
  Nf · Normal                       structural normal form (the counterpart of phino's isNF)
  Context · Canonical               contextualization C(e⊳ctx); the implicit-ρ canonicalisation
  Parallel                          Par/ParB, complete development `devel`, the Takahashi triangle
  Preservation · Diamond            WF preserved under reduction; the WF-relativized diamond
  Confluence                        the headline `confluence`
  Equivalence                       `≡` (convertibility) as an Equivalence on well-formed terms
  Reduce · Render · Rules           executable reducer + reduce_sound; pretty-printer; rule table
  RuleSchema · RuleData             rule tags generated from phino by the fidelity lock
  Abstract/Rewriting                Diamond / Confluent vocabulary + the church_rosser bridge
.github/   regen-rules.sh · gen-rules.py · gen-rule-data.py · phino_render.py · difftest.sh
           test_*.py (generator unit tests) · axioms.lean · requirements.txt · workflows/
Makefile   `make` builds and checks everything CI checks, except difftest
```

CI runs single-purpose workflows, each on push to `master` and on pull requests, against pinned
phino:

* **build** — installs elan and runs `lake exe cache get`, then `make`: the generator unit tests
  (`.github/test_*.py`); `Rules.lean` and `RuleData.lean` generated from the pinned phino
  (`.github/regen-rules.sh`); `lake build`; then a `sorry`/`admit`/`axiom` source gate **and** a
  `#print axioms` gate (`.github/axioms.lean`) on the headline results. `gen-rule-data.py`'s
  fidelity lock fails the build on rule-structure drift.
* **difftest** — installs the pinned phino binary (`.phino-version`, verified against
  `.phino-sha256`), then runs `make difftest`; it fails if our reducer disagrees with phino.
* **phino-latest** — weekly, fails when `.phino-version` lags behind phino's newest release, so a
  stale pin is reported instead of silently narrowing `difftest`.

The two Lean workflows share a composite action (`.github/actions/setup-lean`) that caches
`~/.elan` and `.lake` so Lean and mathlib are not re-downloaded each run. The standard objectionary
hygiene checks run alongside.

## Stack

Lean 4 (`leanprover/lean4:v4.30.0`) and mathlib4 (pinned in `lakefile.toml`), built with Lake.
Abstract rewriting is built on mathlib's `Prop`-valued `Relation` API.

[paper]: https://github.com/objectionary/calculus-paper
[phino]: https://github.com/objectionary/phino
