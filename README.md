<!--
SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
SPDX-License-Identifier: MIT
-->

# Confluence of φ-Calculus Normalization (Lean 4)

[![build](https://github.com/objectionary/proof/actions/workflows/build.yml/badge.svg)](https://github.com/objectionary/proof/actions/workflows/build.yml)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](https://github.com/objectionary/proof/blob/master/LICENSE.txt)

This repository holds a computer-checked proof
  that simplifying a φ-calculus program gives the same result
  no matter in which order you apply the simplification rules.

The φ-calculus is the small formal language behind [EO].
A program in it is a *term*,
  and a fixed set of *rules* rewrites a term, one step at a time,
  into a simpler one.
Often several rules apply at once, or one rule applies in several places,
  so you have a choice of what to rewrite next.
The property proved here, called **confluence** (or **Church–Rosser**),
  says that the choice never matters:
  any two ways of rewriting the same term
  can always be continued until they meet at the same term.

The proof is written in [Lean 4],
  a programming language that is also a *proof assistant*:
  a program that checks every step of a mathematical proof.
If Lean accepts the proof,
  you do not need to trust the reasoning,
  only the statement of the theorem and the few definitions it uses.

The rules are the ones implemented by [`phino`][phino],
  the reference tool for the φ-calculus.
The [paper] that defines the calculus
  generates its table of rules (Fig. 4) from `phino` too,
  so this proof, the paper, and the tool all talk about the same rules.
The proof replaces an earlier one, still in this repository's history,
  that covered only a smaller version of the calculus.

Lean reports that the main theorem, `PhiConfluence.confluence`,
  depends only on the axioms `propext` and `Quot.sound`,
  two standard parts of Lean's logic.
It uses no `sorry` (Lean's placeholder for a missing proof)
  and no `Classical.choice` (the axiom of choice).

## Key terms

* **Term** — a φ-calculus expression.
  It is one of six kinds:
    a *formation* `⟦B⟧`, an object with a list `B`
    of named attributes (its *bindings*);
    an *application* `e(τ↦e')`, which gives attribute `τ` of `e`
    the value `e'`;
    a *dispatch* `e.τ`, which takes attribute `τ` of `e`;
    the global object `Φ`;
    the current object `ξ`;
    or `⊥`, the dead object that results from an error.
* **Attribute** — the name of a binding.
  It is a plain label such as `x`,
    one of the special names `φ` and `ρ` (`ρ` is the object's parent),
    or a *positional* name `αᵢ`, meaning "the attribute at position `i`".
  A binding `x↦∅` is *void*, because it has no value yet;
    a binding `x↦e` is *attached*.
  The special bindings `λ` and `Δ` hold native code and raw data;
    they are called *assets*.
* **Step** — `e ⟶ e'` means one rule rewrites `e` into `e'`,
    anywhere inside it.
  `e ⟶∗ e'` means zero or more steps.
* **Redex** — a place inside a term where a rule can fire.
* **Normal form** — a term with no redex, so no rule can fire.
  `nf e` means "`e` is in normal form".
* **Well-formed** — a term with no repeated attribute names in any formation
    and no positional name used as a formation's attribute.
  Lean calls this `WF`.

## The theorem

The relation `⟶` uses the rules of `phino` version 0.0.138
  (`dd, dc, dca, null, over, stop, miss, stay, alpha, overa, amiss, dot, copy, dl`),
  applied anywhere inside a term.
The fifteenth `phino` rule, `dotg`,
  fires only on a whole program,
  which `phino rewrite` never receives,
  so the proof leaves it out.

The theorem, `PhiConfluence.confluence`, says:

> For every well-formed term `e`, if `e ⟶∗ e₁` and `e ⟶∗ e₂`,
> then some term `e₃` exists with `e₁ ⟶∗ e₃` and `e₂ ⟶∗ e₃`.

Some terms rewrite forever: `⟦x↦y,y↦x⟧.x` never reaches a normal form.
So the usual shortcut, Newman's lemma,
  which derives confluence only for systems where rewriting always stops,
  does not apply.
The proof uses *parallel reduction* instead,
  explained in [Proof strategy][strategy].

The theorem is deliberately narrower
  than "the rules of Fig. 4 exactly as printed";
  the [differences from the paper][differences] are listed and explained below.
The paper itself proves no confluence theorem.
It *assumes* confluence when it defines two terms as equal
  if their normal forms are identical.

### Why only well-formed terms

The Lean definition of a formation is deliberately looser
  than the paper's grammar:
  it allows repeated attribute names and positional names as attributes.
The well-formedness condition `WF` puts back the paper's own two restrictions.
They matter for different reasons.

* **No positional name as a formation attribute (`legalKey`)
    is required for confluence.**
  Without it, the theorem is false.
  Take a malformed term `⟦B₁, αᵢ↦e₁, B₂⟧(αᵢ↦e₂)`
    whose void attribute sits at position `i`.
  The `alpha` rule renames the argument and yields an object,
    while the `over` rule yields `⊥`,
    and those two results can never meet (difference 8).
  The proof uses exactly this condition
    (`lookup_alpha_absent_of_wf`,
    and the `over` and `copy` cases of `par_triangle`).
  It matches `phino`, whose parser rejects such terms.
* **Unique attribute names (`Nodup`, Def. Binding 4.8)
    keep the model faithful to the paper;
    no known example needs them for confluence.**
  The proof carries this condition but never uses it.
  It stays for three reasons:
    the paper's Def. Binding requires it;
    it makes our attribute lookup, which takes the first match,
    agree with `phino`'s lookup (difference 6);
    and every rewriting step preserves it.

`phino` once printed a term with a repeated name:
  `⟦ρ↦⟦⟧⟧` came out as `⟦ρ↦⟦ρ↦∅⟧, ρ↦∅⟧`, with two `ρ` bindings.
That was a printer bug, contradicting the paper's definition
  that `phino`'s own parser enforces,
  and `phino` fixed it in **#748**.
Our model always gave `⟦ρ↦⟦ρ↦∅⟧⟧`, so it now agrees with `phino`.

## Verify it yourself

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh   # one-time: Lean's toolchain manager
pip install -r .github/requirements.txt                  # one-time: Python deps of the generators
make                        # green ⇒ every theorem is kernel-checked and axiom-clean, as in CI
lake exe demo               # the rules + example reductions, by the project's own reducer
make difftest               # our reducer vs `phino rewrite --normalize` (needs phino on PATH)
```

`make` needs GNU Make 4.3 or newer.
It downloads prebuilt parts of [mathlib], Lean's standard mathematics library.
It generates the rule files from the pinned version of `phino`,
  and regenerates them only when `.phino-version` or a generator changes.
It runs the generators' unit tests,
  builds the proof with `lake build`,
  and checks that no main theorem depends on a forbidden axiom.

The rule files `Rules.lean` and `RuleData.lean` are not kept in Git.
They are generated from the `resources/normalize/*.yaml` files
  of the `phino` version named in `.phino-version`,
  the same files the paper's Fig. 4 comes from,
  so they cannot drift away from `phino`.

The project also contains a small program that simplifies terms,
  the *reducer*.
The theorem `reduce_sound` proves every step the reducer takes
  is a genuine `⟶` step.
`make difftest` runs the reducer and `phino` on the same programs
  and checks they reach the same normal forms.
To see which axioms any result depends on,
  run `#print axioms <name>` in Lean.

`lake exe demo` prints the rules in the paper's notation,
  then prints the reducer's step-by-step simplification of example programs.

## The rules

The paper's rule figure (`operators.tex`) is the primary source,
  and `phino`'s `resources/normalize/*.yaml` files
  (shown by `phino explain --normalize`) are its executable version.
In the table below, `C(e⊳ctx)` is *contextualization*:
  it resolves the current-object references `ξ` inside `e` against `ctx`
  (paper, Fig. "Contextualization by induction").
`ordinal(B, i)` is the name of the attribute at position `i` of `B`,
  counted as described in the note (†).

| `phino` rule | Lean `Step` constructor | Pattern → result | Side condition |
|---|---|---|---|
| `dot`   | `Step.dot`   | `⟦B₁,τ↦e₁,B₂⟧.τ → C(e₁⊳⟦B₁,B₂,ρ↦∅⟧)(ρ↦⟦B₁,τ↦e₁,B₂⟧)` | `nf e₁` ∧ not both `λ∈B` and `Δ∈B` (`ρ↦∅` only when `B₁,B₂` lack `ρ`) |
| `dotg`  | — (difference 10) | same, `(ρ↦Φ)` instead | the formation is the whole program |
| `copy`  | `Step.copy`  | `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) → ⟦B₁,τ↦e₁,B₂⟧` | `e₁` has no `ξ` ∧ `nf e₁` (difference 7) |
| `alpha` | `Step.alpha` | `⟦B⟧(αᵢ↦e) → ⟦B⟧(τ↦e)` | `τ = ordinal(B, i)` is void (†) |
| `overa` | `Step.overa` | `⟦B⟧(αᵢ↦e) → ⊥` | `ordinal(B, i)` is attached |
| `amiss` | `Step.amiss` | `⟦B⟧(αᵢ↦e) → ⊥` | `B` has no position `i` (†) |
| `stay`  | `Step.stay`  | `⟦B₁,ρ↦e₁,B₂⟧(ρ↦e₂) → ⟦B₁,ρ↦e₁,B₂⟧` | — |
| `over`  | `Step.over`  | `⟦B₁,τ↦e₁,B₂⟧(τ↦e₂) → ⊥` | `τ≠ρ` (attached attribute) |
| `stop`  | `Step.stop`  | `⟦B⟧.τ → ⊥` | `τ∉B` ∧ `φ∉B` ∧ `λ∉B` |
| `null`  | `Step.null`  | `⟦B₁,τ↦∅,B₂⟧.τ → ⊥` | — (void attribute) |
| `miss`  | `Step.miss`  | `⟦B⟧(τ↦e) → ⊥` | `τ∉B` ∧ `τ` is not positional |
| `dl`    | `Step.dl`    | `⟦B⟧ → ⊥` | `λ∈B` ∧ `Δ∈B` |
| `dd`    | `Step.dd`    | `⊥.τ → ⊥` | — |
| `dc`, `dca` | `Step.dc` | `⊥(τ↦e) → ⊥`, `⊥(αᵢ↦e) → ⊥` | — (one Lean rule covers both) |

(†) **Positions skip the assets and the parent.**
When counting positions, `phino` skips the assets `λ` and `Δ` (phino #749)
  and the parent `ρ`, and so does `ordinal` in `Attributes.lean`.
In `⟦λ⤍Fn, x↦∅, ρ↦∅⟧`, `x` is at position `0`,
  and there is no position `1`.
This follows the paper's Def. Ordinal and Def. Domain.
The three positional rules `alpha`, `overa`, and `amiss`
  cover every possible position,
  so one of them always applies to a positional argument of a formation.

Four more rules, `Step.congDispatch`, `Step.congAppFn`, `Step.congAppArg`,
  and `Step.congForm`, let any rule fire *inside* a term:
  in the object of a dispatch, in either side of an application,
  or in the value of a formation's binding.
This matches the paper (`operators.tex`),
  which says "rules may be applied in any order".

At the top of a term, at most one rule applies, with one exception:

* On a dispatch `⟦B⟧.τ`, the rule depends on attribute `τ`:
    `dot` if it is attached, `null` if it is void,
    and `stop` if it is missing and `B` holds neither `φ` nor `λ`.
  On `⊥.τ`, `dd` applies.
  A dispatch of a missing attribute on a formation holding `φ` or `λ`
    is already normal, because `phino` dropped its `phi` rule,
    and so are terms like `Φ.τ` and `ξ.τ`.
* On an application `⟦B⟧(τ↦e)` with a named `τ`,
    the rule depends on attribute `τ`:
    `stay` if it is `ρ` and attached,
    `over` if it is another attached name,
    `copy` if it is void and `e` is normal and has no `ξ`,
    and `miss` if it is missing.
  With a positional `αᵢ`, the rule is `alpha`, `overa`, or `amiss`,
    depending on `ordinal(B, i)`.
  On `⊥(…)`, `dc` applies.
* **The exception:** `dl` competes with every other rule
    on a formation holding both `λ` and `Δ`.
  Each such conflict still ends at `⊥`, except with `dot`,
    which would move the formation into a `ρ` binding
    and leave a stuck `…(ρ↦⊥)`.
  That is why `phino` 0.0.138 forbids `dot` on such a formation
    (phino #1395), and `Step.dot` does too.

## Differences from the paper

The model follows the **current** paper,
  whose Fig. 4 is generated by current `phino` (`phino explain --normalize`).
The items below record where *older* published versions differed,
  which choices limit the theorem's scope,
  and which assumptions it makes.
None of them is a gap against the current paper.

1. **`over` needs an *attached* attribute.**
   The current Fig. 4 and our `over` both require `τ` to have a value,
     as in `⟦B₁,τ↦e₁,B₂⟧(τ↦e₂)`.
   Def. 4.9 (Formation) defines membership `τ∈b` to include void attributes,
     so a careless reading would let `over` fire on a void attribute too.
   There it would compete with `copy`,
     and their results, an object and `⊥`, could never meet.
   The published arXiv v9 PDF, built with an older `phino`,
     printed exactly that looser form.
   We follow the current form, where the two rules never compete.
2. **`dot` and `copy` wait for normal forms.**
   They fire only when the value they move is already normal.
   This forces inner parts to simplify first,
     gives each rule a single way to fire,
     and removes the question of whether `dot` or `copy` goes first,
     which blocked the old proof.
   It also means that whether a rule may fire can change
     as other parts of the term simplify,
     which is the main difficulty of the proof.
3. **`copy` takes one small step.**
   The current paper's `copy` is the one-step, normal-form-guarded rule we use.
   An older version (arXiv v9) had a rule `Rcopy`
     that fully simplified its argument inside one rule (`C(e⊳eς) ⟶∗ n`).
   That rule assumed normal forms are unique, which is confluence itself,
     so a proof based on it would be circular.
   The old form is not modelled.
4. **Assets `λ` and `Δ` are not rewritten.**
   Only `dl` looks at them, turning a formation that holds both into `⊥`.
   The paper evaluates them separately, in its **Morphing**
     (`fig:morphing`, where `Mlambda` calls native code)
     and **Dataization** (`fig:dataization`) functions.
   Those functions have state and side effects
     and depend on the host machine,
     so the question there is whether they are deterministic,
     not whether they are confluent.
   Here `λ` and `Δ` are inert values
     (`Binding.lambda` and `Binding.delta`) that never fire.
   This boundary comes from the paper's own structure;
     it is not unfinished work.
   It is also why the paper's Appendix-A examples are checked with `difftest`
     (against a merged `runtime.phi`) instead of being rewritten in Lean.
5. **Every rule `phino rewrite` applies is modelled.**
   The rule `dot` puts the dispatched formation into the result's `ρ`,
     which is what lets some terms rewrite forever.
   It came first, with its normal-form guard and contextualization;
     `copy` and `alpha` followed.
   Issue #73 updated the rules to `phino` 0.0.138:
     `phi` is gone;
     `overa`, `amiss`, and `dl` are new;
     `dot` contextualizes against `⟦B₁, B₂⟧`;
     and `copy` accepts `⊥`.
6. **Attribute names are unique (Def. 4.8).**
   With unique names, our lookup, which takes the first match,
     agrees with `phino`'s lookup, which accepts a match at any position.
   The `Nodup` part of `WF` states this assumption.
7. **`copy` requires its argument to be normal and free of `ξ`.**
   `Step.copy` fills a void attribute,
     `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) → ⟦B₁,τ↦e₁,B₂⟧`,
     with no contextualization.
   `phino`'s printed figure shows only the normal-form condition,
     because its printer hides the `ξ` condition,
     but `phino`'s engine enforces it.
   When `e₁` has no `ξ`, contextualization leaves it unchanged,
     and Lean proves this (`contextualize_eq_self` in `Parallel.lean`).
   So leaving contextualization out of `copy` changes nothing.
   Requiring no `ξ` also
     (a) keeps `copy` independent of the surrounding term,
     (b) keeps `copy` inside the part of the calculus
     tested before the proof began,
     and (c) makes `difftest` meaningful:
     without the condition, `⟦x↦∅⟧(x↦ξ)` would give a different result.
   The paper's author is updating the paper's figure and `phino` to this form,
     so the model and the paper match exactly.
   The single normal-form test `nf` includes the `ξ` condition
     for void applications, just as `phino`'s `isNF` does.
8. **A formation's attributes are never positional.**
   The paper's grammar (`syntax.tex`) uses positional names `αᵢ`
     only in application arguments;
     a formation's attributes are `φ`, `ρ`, or labels.
   The Lean `Binding` accepts any name, including `Attr.alpha`,
     so it can represent a malformed formation with a positional attribute.
   The `legalKey` part of `WF` rules such formations out.
9. **Every formation has a parent attribute `ρ`.**
   This is modelled, not a difference;
     see [The parent attribute][parent].
10. **The rule `dotg` is not modelled.**
    `phino` uses `dotg` instead of `dot`
      when the dispatched formation is the whole program,
      and it puts `Φ` into the result's `ρ`.
    The model follows `phino rewrite` on a single expression,
      which is never the whole program,
      so `dot` always fires and `dotg` never does.

Two more loose spots in the model are intentional.
`Step.alpha` and `Step.copy` do not themselves require well-formedness;
  the theorem's `WF` condition excludes malformed terms for all rules at once,
  and `phino` does not check this per rule either.
Also, `Nodup` ignores the assets,
  so a formation may hold two `λ` or two `Δ` bindings.
That is harmless while assets never fire,
  and would need tightening only if they ever do.

## The parent attribute

The paper (`foundations.tex`, Def. Parent) and `phino`
  treat **every formation as having a parent attribute `ρ`**,
  void until something sets it,
  much like `this` in other languages.
The paper's grammar (`syntax.tex`) does not require `ρ`,
  so `⟦⟧` is a valid formation.
Instead, `phino` adds `ρ↦∅` at the end of every formation that lacks one,
  at every depth:
  `⟦x↦Φ⟧` becomes `⟦x↦Φ, ρ↦∅⟧`.
An explicit `ρ` stays where it is and is never duplicated.

Without this, the model would disagree with `phino` and the paper
  in three ways:

* A different rule could fire:
    `phino` rewrites `⟦⟧(ρ↦Φ)` by `copy` to `⟦ρ↦Φ⟧`,
    but without `ρ` the rule `miss` gives `⊥`.
* Positional arguments would land elsewhere,
    because the added `ρ` counts as a position for `alpha`:
    `⟦x↦∅⟧(~1↦Φ) ⟶ ⟦x↦∅, ρ↦Φ⟧`,
    where `~1` is `phino`'s spelling of `α₁`.
* Normal forms would differ,
    because every formation in a `phino` normal form carries `ρ↦∅`.

`Canonical.lean` models the parent attribute:

* `canon` and `canonB` add `ρ↦∅` to every formation without `ρ`,
    at every depth, exactly as `phino` does.
* `Canonical` and `CanonicalB` state that every formation has a `ρ`.
* `canon_canonical` proves that `canon` always produces such a term.
* `wf_canon` proves that `canon` keeps a term well-formed,
    because it adds `ρ` only where none exists.
* `step_canonical` proves that rewriting keeps every formation's `ρ`,
    so the terms `phino` works with stay that way under `⟶`.

Because such terms are well-formed, the main theorem covers them,
  so it is a theorem about **the calculus `phino` actually implements**,
  not a version without `ρ`.
The added `ρ` never threatened confluence:
  it is a default value, not a rule,
  and it only moves `ρ`-applications from `miss` to `copy`,
  which creates no new conflict between rules.
It was a question of faithfulness,
  settled by the three lemmas above
  and by `difftest`, which now matches `phino`
  even on the cases that differed before `canon` existed,
  such as `⟦⟧(ρ↦Φ)` and plain value formations.

## Design decisions

The paper ([`objectionary/calculus-paper`][paper]) defines the calculus
  in ordinary mathematical prose.
Its Fig. 4 rules and Appendix-A example reductions
  **are generated by `phino`**
  (`\iexec{phino explain --normalize}` and `phino rewrite`),
  and its CI checks them.
[`phino`][phino] is therefore the authoritative, executable definition,
  in `resources/normalize/*.yaml`.
The earlier proof in this repository's history
  served only as a model for the proof technique
  (the parallel-reduction skeleton and the `Record` design).
Because the paper's rules and examples come from `phino`,
  matching the paper means matching `phino`,
  and running both can test that.
This work found two `phino` bugs, both since fixed:
  it counted assets as positions (phino #749),
  and it printed a duplicate `ρ` (phino #748).
In both cases the model already did what the paper says.

| Decision | Reason |
|---|---|
| **Use `phino` and the paper's LaTeX source as the reference**, never the arXiv PDF | The PDF is an old build; the LaTeX source regenerates its rules from current `phino`. |
| **Prove confluence through parallel reduction** | Some terms rewrite forever, so Newman's lemma cannot be used; the parallel-reduction method (Tait, Martin-Löf, Takahashi) works either way. |
| **Build on mathlib's `Relation` library** | It already proves that the diamond property implies confluence, so less new code is needed. |
| **Keep attribute names** (`φ`, `ρ`, `αᵢ`, labels) | They match the paper and `phino` and make contextualization and positions natural; numbering variables instead (de Bruijn indices) would hide what the names mean. |
| **Define "normal form" directly, like `phino`'s `isNF`**, not as "no step possible" | This avoids a circular dependency between Lean files and the circularity of the old big-step `copy`; it depends only on the term itself, so it makes sense before confluence is known. One definition covers every rule, including `copy`'s `ξ` condition. |
| **Keep a runnable reducer next to the rules, linked by `reduce_sound`** | The demo can run and print its steps, and a proof guarantees each printed step follows the rules — a closer link than `phino` has, since its Haskell engine is not proven against its YAML rules. |
| **Leave contextualization out of `copy`** | With no `ξ` in the argument, it changes nothing, and it keeps `copy` in the tested part of the calculus (difference 7). |
| **State the theorem for well-formed terms only** | `legalKey` is needed for confluence; `Nodup` keeps the model faithful. Both are the paper's own rules (see [Why only well-formed terms][wf]). |

## Proof strategy

The proof goes in six steps.

1. Define one rewriting step `⟶` (`Step`):
     the `phino` rules plus the four rules that let them fire inside a term.
2. Define *parallel reduction* `Par`,
     which rewrites any number of redexes in one go,
     and the *complete development* `devel e`,
     which rewrites all the redexes `e` has at once.
3. Prove that one step is a parallel step,
     and a parallel step is a sequence of ordinary steps,
     so many steps of either kind reach the same terms (`redMany_eq`).
4. Prove the *Takahashi triangle*:
     for a well-formed `e`, if `e` reaches `u` in one parallel step,
     then `u` reaches `devel e` in one parallel step
     (`WF e → Par e u → Par u (devel e)`).
   So any two parallel steps from `e` meet again at `devel e`;
     this is the *diamond property*.
5. A general theorem (`Abstract.Diamond.confluent`,
     through mathlib's `church_rosser`)
     turns the diamond property into confluence,
     and step 3 carries it over to `⟶`.
6. Define equality of terms (`≡`)
     as "the terms can be rewritten to a common term";
     confluence makes it a proper equivalence on well-formed terms.

The hardest parts were proving that contextualization and rewriting
  can happen in either order (`par_contextualize_ctx`),
  handling rules whose permission to fire changes
  as other parts simplify,
  and handling `dot`'s `ρ`, which lets terms rewrite forever.

### Three design choices inside the proof

Each of these was checked against Lean `v4.30.0` and mathlib
  before the full proof was written.

1. **Well-formedness is a condition, not a type.**
   `WF` and `WFB` (`WellFormed.lean`, which depends only on `Syntax`)
     are a condition assumed by the diamond lemma and the main theorem.
   Building it into the type of bindings instead
     would force rewriting `Syntax`, `Step`, and `Attributes`.
   The proof that rewriting keeps terms well-formed
     (`WF.step` and `WF.par` in `Preservation.lean`)
     rests on one fact:
     rewriting a binding's value never changes the attribute names
     (`domain_append`, `domain_set`).
2. **Parallel reduction on binding lists is defined by hand.**
   `Par` and `ParB` are defined together,
     and `ParB` walks a binding list one element at a time.
   Lean rejects the shortcut through `List.Forall₂`,
     because it does not accept that kind of nested definition here.
   Only `Step.congForm` splits a list into
     "before, this binding, after",
     and `parB_set` handles that split once.
   Induction over both definitions uses `Par.rec` with `motive_2`.
   The lemma `redMany_form_cons` is proved directly
     (by `induction … generalizing` and `form_step_inv`),
     because the general `ReflTransGen.lift` is wrong here:
     `stay` turns an application into a formation.
3. **Rule guards are checked on the already-rewritten part.**
   `dot` places the formation in two spots of its result,
     so a conflict between `dot` and a rewrite of a neighbouring binding
     can take more than one step on each side to resolve.
   That rules out Huet's simpler method,
     which needs such conflicts to resolve in one step.
   A parallel step rewrites all copies at once, so it has no such problem.
   The parallel versions of the guarded rules test "is normal"
     on the rewritten value `e₁'`, not on the original `e₁`;
     for example, `Par.dot` reads it from `develB bs` through `lookup`.
   That keeps `devel` simple and makes the triangle hold.

**Limiting the diamond to well-formed terms.**
The general theorem (`church_rosser`, `Abstract.Diamond.confluent`)
  needs the diamond property for *all* terms,
  but it fails for malformed ones,
  where `alpha` and `over` conflict.
So the proof uses `ParWF a b := WF a ∧ Par a b`,
  a parallel step from a well-formed term.
Since rewriting keeps terms well-formed (`WF.par`),
  `ParWF` has the diamond property for all terms,
  trivially so when the start is not well-formed.
The general theorem then gives confluence of `ParWF`,
  and `redMany_eq` carries it back to `⟶` on well-formed terms.
Only the starting term must be well-formed,
  so no new general lemma was needed (`Diamond.lean`).

### Why confluence was expected to hold

Before the proof was written, the main risk was that rule guards,
  which change as a term simplifies,
  might break the diamond property.
Two checks addressed it.

The first was a test:
  seven hand-written programs and the paper's Appendix-A examples,
  each simplified with the rules tried in shuffled order (`--shuffle`)
  and with single rules fired at unusual positions.
No run gave a different result.

The second was an analysis, which the proof later made rigorous:

* **Rules never compete at the top of a term.**
  On a dispatch `⟦B⟧.τ`, the rules `dot`, `null`, `stop`, and `dd`
    exclude each other,
    depending on whether `τ` is attached, void, or missing,
    whether `B` has `φ`, and what the dispatched term is.
  On an application `⟦B⟧(τ↦e)`, the rules `copy`, `alpha`, `overa`,
    `amiss`, `over`, `stay`, `miss`, and `dc` exclude each other,
    depending on the attribute's state, on the kind of name
    (positional names go to `alpha`, `overa`, or `amiss`,
    labels to `copy`, `over`, or `miss`, and `ρ` to `stay`),
    and on what the applied term is.
  The later rule `dl` competes with others,
    but always ends at `⊥`, because `dot` is barred there (phino #1395).
  This relies on the well-formedness conditions:
    no attribute name repeats, so each attribute has one state,
    and positional names never name a formation's attribute.
* **Conflicts deeper inside a term always resolve.**
  If `dot` copies a part that still has redexes,
    rewriting that part before or after the copy
    gives the same normal form.
  If `over`, `null`, `stop`, `miss`, `dc`, or `dd`
    throws a part away and yields `⊥`,
    whatever happened inside that part no longer matters.
  That is why these rules need no guard,
    and why confluence holds even though some terms rewrite forever.
* **Changing guards cause no harm.**
  Rewriting inside `e₁` can make it normal
    and so allow a `dot` or `copy` on the outside,
    which breaks the most naive version of the triangle.
  But while `e₁` is not normal, no outer rule competes with it,
    and rewriting a neighbour never disables a rule that could already fire.
  The third design choice above relies on exactly this.

Other methods were considered and rejected:
  Huet's one-step method, because `dot` copies terms;
  orthogonality, because some rules mention the same `τ` twice;
  Hindley–Rosen, because mathlib has no support for it;
  and decreasing diagrams,
  because Lean has no library for them and they are not needed.

## Faithfulness

Lean guarantees the proof is **correct**:
  the theorem follows from the definitions.
It cannot guarantee the definitions are **faithful**,
  meaning they describe the φ-calculus the paper means,
  because the paper is written in prose.
Several independent checks narrow that gap:

* **A human needs to read only a little.**
  To trust the result, you need to read only `Syntax`, `Step`,
    the definition of `⟶∗`, and the statement of `confluence`,
    a few dozen lines in total.
* **The printed rules come from `phino`.**
  The rule table (`Rules.lean`) is generated from the pinned `phino`
    before every build, so it cannot drift from `phino`.
  The rules the proof uses, `Step`, are written by hand,
    because the proof needs to look at them case by case,
    and `difftest` checks they behave like `phino`.
* **The results are compared with `phino`.**
  `Difftest.lean` and `.github/difftest.sh` simplify each test program
    with both `phino rewrite --normalize` and our reducer
    and check the results are equal.
  All 26 programs match.
  Together they exercise every modelled rule,
    including how positions skip `λ`, `Δ`, and `ρ`,
    on programs that end in `⊥` and on programs that end in real objects.
  The paper's Appendix A is generated with the same `phino rewrite`,
    so this also reproduces the paper's examples,
    except those that need `λ` or `Δ` to run.
* **CI checks the axioms.**
  The main results (`confluence`, `conv_equivalence`, `reduce_sound`,
    `par_triangle`, `parWF_diamond`, and `nf_iff`)
    may depend only on `propext` and `Quot.sound`,
    never on `sorryAx`, `Classical.choice`, or `native_decide`.

CI or Lean checks every arrow in this chain:

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

To trust the result, you must trust exactly three things:
  (a) Lean's kernel, the small core that checks proofs;
  (b) the definitions and the theorem statement;
  and (c), for the demo and CI only,
  the code that prints and parses terms, and `phino` itself.
The proof adds nothing to this list.

An optional improvement would generate `Step` itself from `phino`'s YAML files,
  not just the printed table,
  so the proof and the paper's figure would come from one source.
Today `Step` is written by hand and checked against `phino` by `difftest`.
Generating it would make the match structural instead of tested.
It would not change whether the proof is correct.

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

CI runs separate workflows on every push to `master` and every pull request,
  all against the pinned `phino`:

* **build** installs Lean, downloads mathlib (`lake exe cache get`),
    and runs `make`.
  That runs the generators' unit tests (`.github/test_*.py`),
    generates `Rules.lean` and `RuleData.lean`
    from the pinned `phino` (`.github/regen-rules.sh`),
    builds the proof (`lake build`),
    rejects any `sorry`, `admit`, or `axiom` in the source,
    and checks the main results' axioms (`.github/axioms.lean`).
  `gen-rule-data.py` also fails the build
    if the structure of `phino`'s rules changes.
* **difftest** installs the pinned `phino` binary
    (named in `.phino-version` and verified against `.phino-sha256`)
    and runs `make difftest`,
    which fails if our reducer and `phino` disagree.
* **phino-latest** runs weekly
    and fails when `.phino-version` falls behind the newest `phino` release,
    so an outdated version is reported
    instead of quietly limiting `difftest`.

The two Lean workflows share one setup action (`.github/actions/setup-lean`)
  that caches `~/.elan` and `.lake`,
  so Lean and mathlib are not downloaded on every run.
The usual objectionary checks for style and licensing run alongside.

## Stack

The proof uses Lean 4 (`leanprover/lean4:v4.30.0`)
  and mathlib4 (pinned in `lakefile.toml`),
  and it builds with Lake, Lean's build tool.
The general rewriting theory rests on mathlib's `Relation` library.

[EO]: https://github.com/objectionary/eo
[Lean 4]: https://leanprover.github.io
[mathlib]: https://github.com/leanprover-community/mathlib4
[paper]: https://github.com/objectionary/calculus-paper
[phino]: https://github.com/objectionary/phino
[strategy]: #proof-strategy
[differences]: #differences-from-the-paper
[parent]: #the-parent-attribute
[wf]: #why-only-well-formed-terms
