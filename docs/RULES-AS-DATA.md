<!--
SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
SPDX-License-Identifier: MIT
-->

# Rules as checked data — pinning `Step` to phino (M5, proposed)

**Status.** The deriver (`scripts/gen-rule-data.py`) is implemented and tested.
The Lean layer below is a **reviewed draft**: it was written without a local Lean
toolchain, so the *definitions and the theorem statement* are the contract, and the
*proofs* are mechanical case-bashes that still need to be compiled and nudged into
shape. Nothing here is imported into `PhiConfluence.lean` yet, so the green build and
the `[propext, Quot.sound]` axiom gate are untouched until this is compiled and wired
in (see "Wiring", below).

## Why this exists, and what it does (and does not) buy

Today the eleven rules live in the repo **twice**: once as the hand-written `Step`
relation (the object the confluence theorem is about) and once as
`normalizationRules : List RuleSpec` in `Rules.lean` — display strings generated from
phino, with **no kernel-checked link** to `Step`. So "our `Step` matches phino" rests
on a human reading both plus `difftest` (which compares only one strategy's normal
forms on a curated corpus). That is the faithfulness gap.

This milestone closes the gap *mechanically* for the **root rules**:

```
phino YAML ──gen-rule-data.py (fidelity lock)──▶ normalizationRuleData : List RuleSpec
                                                         │
                                       RuleSpec.applies  │  (hand-written interpreter)
                                                         ▼
   RootStep  ◀───── conformance : RootStep e e' ↔ ∃ r ∈ normalizationRuleData, r.applies e e'
      │                                                  (kernel-checked)
      │ rootStep_to_step
      ▼
    Step  =  RootStep  +  the four congruence constructors (the compatible closure;
                          phino has no congruence rules — "rules apply anywhere")
```

If phino changes a rule, one of two things breaks the build:

* the change alters the rendered pattern/result/condition → the deriver's **fidelity
  lock aborts** (`scripts/gen-rule-data.py` raises; CI red); or
* the change is absorbed into the regenerated `normalizationRuleData` tags but no
  longer matches `RootStep` → **`conformance` fails to type-check**.

**What it does not buy.** phino's rule *semantics* live in its Haskell — `contextualize`,
`isNF`/`nf`, the domain ordinal `voidAtOrdinal`, `fill` — and are only *named* in the
YAML (e.g. `dot`'s `where: 𝑒2 := contextualize(𝑒1, …)`). Those functions are still
hand-written in Lean (`Context.lean`, `Nf.lean`, `Attributes.lean`) and **trusted** to
match phino regardless of any codegen. So this does not make `Step` "derived from
phino" in the strong sense; it makes the *rule structure* (which redex shape, which
side-conditions, which contractum, per rule) generated data that is **kernel-checked
against `Step`**, while the semantic vocabulary remains a small, explicit trusted
surface. That is the honest ceiling of mechanization while phino is the reference and
its semantics are not themselves formalized.

## ξ-free: data vs display (a bug this surfaced)

`gen-rules.py` claims to strip `copy`'s `ξ`-free guard "so `copy` shows `nf(𝑒1)` only",
but the committed `Rules.lean` still reads `cond := "xi-free(𝑒) and nf(𝑒)"`: the strip
`if k == "xi"` never fires because phino's key is `xi-free`. The clean resolution is the
data/display split this milestone introduces:

* **Data** (`gen-rule-data.py`, this layer) **keeps** `ξ`-free — because `Step.copy`
  carries `xiFree e₁`, so the conformance theorem *needs* it.
* **Display** (`gen-rules.py`) may strip `ξ` for paper-figure parity — a rendering
  choice, not a semantic one.

So `gen-rules.py`'s `if k == "xi"` should be `if k == "xi-free"` (display intent), and
`gen-rule-data.py` deliberately does **not** strip it (proof intent). Filed as a
separate small fix; tracked here so the two generators do not silently disagree.

## The Lean layer (draft — compile before relying on)

### `PhiConfluence/RuleSchema.lean` (hand-written: schema + interpreter)

```lean
-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Step

/-!
# Structured rule schema + interpreter

`RuleSpec` is one normalization rule as interpretable tags (redex shape, side-conditions,
contractum). `RuleSpec.applies r e e'` is its semantics over `Term`, built from the same
primitives `Step` uses (`lookup`, `nf`, `xiFree`, `voidAtOrdinal`, `contextualize`, `fill`).
The generated `normalizationRuleData` (RuleData.lean) is a `List RuleSpec`; `RuleConform`
proves that list equal to the root fragment of `Step`.
-/

namespace PhiConfluence

/-- Which redex a rule fires on: `⊥.a`, `⊥(a↦arg)`, `⟦bs⟧.a`, or `⟦bs⟧(a↦arg)`. -/
inductive RedexShape where
  | dispatchBot | appBot | dispatchForm | appForm
  deriving Repr, DecidableEq

/-- A side condition, read against the redex's `(bs, a, arg)`. -/
inductive Cond where
  | slotVoid | slotAttached | slotAbsent
  | attrNeRho | attrIsRho | attrNotAlpha
  | phiAbsent | phiPresent | noLambda
  | valNf | argXiFree | argNf | alphaVoidOrdinal
  deriving Repr, DecidableEq

/-- The contractum, built from the redex's `(bs, a, arg)`. -/
inductive Contractum where
  | bot | formSame | phiExpand | dotFeedback | copyFill | alphaRename
  deriving Repr, DecidableEq

/-- One rule as data. -/
structure RuleSpec where
  name  : String
  shape : RedexShape
  conds : List Cond
  rhs   : Contractum

/-- A side condition as a `Prop` over the redex's formation `bs`, attribute `a`, argument `arg`. -/
def Cond.holds (bs : List Binding) (a : Attr) (arg : Term) : Cond → Prop
  | .slotVoid         => lookup bs a = .void
  | .slotAttached     => ∃ v, lookup bs a = .attached v
  | .slotAbsent       => lookup bs a = .absent
  | .attrNeRho        => a ≠ .rho
  | .attrIsRho        => a = .rho
  | .attrNotAlpha     => a.isAlpha = false
  | .phiAbsent        => lookup bs .phi = .absent
  | .phiPresent       => lookup bs .phi ≠ .absent
  | .noLambda         => hasLambda bs = false
  | .valNf            => ∃ v, lookup bs a = .attached v ∧ nf v = true
  | .argXiFree        => xiFree arg = true
  | .argNf            => nf arg = true
  | .alphaVoidOrdinal => ∃ i τ, a = .alpha i ∧ voidAtOrdinal bs i = some τ

/-- The contractum as a (partial) `Term`, from the redex's `(bs, a, arg)`. -/
def Contractum.build (bs : List Binding) (a : Attr) (arg : Term) : Contractum → Option Term
  | .bot         => some .bot
  | .formSame    => some (.form bs)
  | .phiExpand   => some (.dispatch (.dispatch (.form bs) .phi) a)
  | .copyFill    => some (.form (fill bs a arg))
  | .dotFeedback =>
      match lookup bs a with
      | .attached v => some (.app (contextualize v (.form bs)) .rho (.form bs))
      | _           => none
  | .alphaRename =>
      match a with
      | .alpha i => match voidAtOrdinal bs i with
                    | some τ => some (.app (.form bs) τ arg)
                    | none   => none
      | _        => none

/-- The semantics of a rule: does `e ↝ e'` by rule `r`? -/
def RuleSpec.applies (r : RuleSpec) (e e' : Term) : Prop :=
  match r.shape, e with
  | .dispatchBot,  .dispatch .bot _       => r.conds = [] ∧ r.rhs = .bot ∧ e' = .bot
  | .appBot,       .app .bot _ _          => r.conds = [] ∧ r.rhs = .bot ∧ e' = .bot
  | .dispatchForm, .dispatch (.form bs) a => (∀ c ∈ r.conds, c.holds bs a .bot) ∧ r.rhs.build bs a .bot = some e'
  | .appForm,      .app (.form bs) a arg  => (∀ c ∈ r.conds, c.holds bs a arg) ∧ r.rhs.build bs a arg = some e'
  | _, _ => False

end PhiConfluence
```

### `PhiConfluence/RuleData.lean` (GENERATED by `gen-rule-data.py`)

This is exactly what the (tested) deriver emits today; commit it via
`python3 scripts/gen-rule-data.py <phino>/resources PhiConfluence/RuleData.lean`:

```lean
-- AUTO-GENERATED by scripts/gen-rule-data.py from objectionary/phino resources/*.yaml.
import PhiConfluence.RuleSchema
namespace PhiConfluence

/-- The φ-calculus normalization rules as structured, interpretable data. -/
def normalizationRuleData : List RuleSpec :=
  [ { name := "alpha", shape := .appForm,      conds := [.alphaVoidOrdinal],           rhs := .alphaRename }
  , { name := "copy",  shape := .appForm,      conds := [.slotVoid, .argXiFree, .argNf], rhs := .copyFill }
  , { name := "dc",    shape := .appBot,       conds := [],                            rhs := .bot }
  , { name := "dd",    shape := .dispatchBot,  conds := [],                            rhs := .bot }
  , { name := "dot",   shape := .dispatchForm, conds := [.slotAttached, .valNf],       rhs := .dotFeedback }
  , { name := "miss",  shape := .appForm,      conds := [.slotAbsent, .attrNotAlpha],  rhs := .bot }
  , { name := "null",  shape := .dispatchForm, conds := [.slotVoid],                   rhs := .bot }
  , { name := "over",  shape := .appForm,      conds := [.slotAttached, .attrNeRho],   rhs := .bot }
  , { name := "phi",   shape := .dispatchForm, conds := [.phiPresent, .slotAbsent],    rhs := .phiExpand }
  , { name := "stay",  shape := .appForm,      conds := [.attrIsRho, .slotAttached],   rhs := .formSame }
  , { name := "stop",  shape := .dispatchForm, conds := [.slotAbsent, .phiAbsent, .noLambda], rhs := .bot } ]

end PhiConfluence
```

### `PhiConfluence/RuleConform.lean` (hand-written: the pin)

```lean
-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.RuleData

/-!
# Conformance: the generated rule data is exactly `Step`'s root fragment

`RootStep` is `Step` minus the four congruence constructors (phino has no congruence
rules; the closure is the project's own). `conformance` pins the phino-derived
`normalizationRuleData` to `RootStep`, and `rootStep_to_step` ties `RootStep` back into
the relation the confluence theorem governs.
-/

namespace PhiConfluence

/-- The eleven root rules of `Step`, without the congruence closure. -/
inductive RootStep : Term → Term → Prop where
  | dd (a : Attr) : RootStep (.dispatch .bot a) .bot
  | dc (a : Attr) (e : Term) : RootStep (.app .bot a e) .bot
  | null {bs a} : lookup bs a = .void → RootStep (.dispatch (.form bs) a) .bot
  | over {bs a e₁ e₂} : lookup bs a = .attached e₁ → a ≠ .rho → RootStep (.app (.form bs) a e₂) .bot
  | stop {bs a} : lookup bs a = .absent → lookup bs .phi = .absent → hasLambda bs = false →
      RootStep (.dispatch (.form bs) a) .bot
  | miss {bs a e} : lookup bs a = .absent → a.isAlpha = false → RootStep (.app (.form bs) a e) .bot
  | stay {bs e₁ e₂} : lookup bs .rho = .attached e₁ → RootStep (.app (.form bs) .rho e₂) (.form bs)
  | phi {bs a} : lookup bs .phi ≠ .absent → lookup bs a = .absent →
      RootStep (.dispatch (.form bs) a) (.dispatch (.dispatch (.form bs) .phi) a)
  | alpha {bs i τ₁ e} : voidAtOrdinal bs i = some τ₁ →
      RootStep (.app (.form bs) (.alpha i) e) (.app (.form bs) τ₁ e)
  | dot {bs a e₁} : lookup bs a = .attached e₁ → nf e₁ = true →
      RootStep (.dispatch (.form bs) a) (.app (contextualize e₁ (.form bs)) .rho (.form bs))
  | copy {bs a e₁} : lookup bs a = .void → xiFree e₁ = true → nf e₁ = true →
      RootStep (.app (.form bs) a e₁) (.form (fill bs a e₁))

/-- Every root step is a `Step` (each constructor maps to the same-named `Step` rule). -/
theorem rootStep_to_step {e e' : Term} (h : RootStep e e') : Step e e' := by
  cases h with
  | dd a => exact .dd a
  | dc a e => exact .dc a e
  | null h => exact .null h
  | over h1 h2 => exact .over h1 h2
  | stop h1 h2 h3 => exact .stop h1 h2 h3
  | miss h1 h2 => exact .miss h1 h2
  | stay h => exact .stay h
  | phi h1 h2 => exact .phi h1 h2
  | alpha h => exact .alpha h
  | dot h1 h2 => exact .dot h1 h2
  | copy h1 h2 h3 => exact .copy h1 h2 h3

/-- **The pin.** The phino-derived rule data denotes exactly `RootStep`. A phino change
that survives the deriver but alters a rule's meaning breaks this theorem. -/
theorem conformance {e e' : Term} :
    RootStep e e' ↔ ∃ r ∈ normalizationRuleData, r.applies e e' := by
  constructor
  · intro h
    -- forward: each RootStep constructor exhibits its generated entry as the witness.
    cases h with
    | dd a => exact ⟨_, by simp [normalizationRuleData], by simp [RuleSpec.applies]⟩
    | dc a e => exact ⟨_, by simp [normalizationRuleData], by simp [RuleSpec.applies]⟩
    | null h =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h]⟩
    | over h1 h2 =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h1, h2]⟩
    | stop h1 h2 h3 =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h1, h2, h3]⟩
    | miss h1 h2 =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h1, h2]⟩
    | stay h =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h]⟩
    | phi h1 h2 =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h1, h2]⟩
    | alpha h =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h]⟩
    | dot h1 h2 =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h1, h2]⟩
    | copy h1 h2 h3 =>
        exact ⟨_, by simp [normalizationRuleData],
          by simp [RuleSpec.applies, Cond.holds, Contractum.build, h1, h2, h3]⟩
  · rintro ⟨r, hr, ha⟩
    -- backward: enumerate the 11 entries; each `applies` reconstructs its RootStep rule.
    -- `fin_cases hr` splits the list; `RuleSpec.applies` then forces the redex shape and,
    -- via `Cond.holds`/`Contractum.build`, the side-conditions and contractum.
    fin_cases hr <;>
      first
      | (obtain ⟨hc, hb⟩ := ha; · skip)  -- PUZZLE: per-entry, destructure conds/build then
                                         -- `cases e` to expose the redex and apply the
                                         -- matching `RootStep` constructor. See notes below.
      | skip

end PhiConfluence
```

The backward direction is the one genuine puzzle: after `fin_cases hr` each goal has a
concrete `r` and `ha : r.applies e e'`; `simp [RuleSpec.applies] at ha` forces `e` into
the rule's redex shape (`dispatch (form bs) a` etc.), `Cond.holds` turns the condition
list into the rule's hypotheses, `Contractum.build … = some e'` pins `e'`, and the
matching `RootStep.<name>` closes it. It is mechanical but verbose; left as a
**Puzzle** to complete against the compiler rather than guess blind here.

## Wiring (once compiled green)

1. Add `RuleSchema.lean`; `python3 scripts/gen-rule-data.py <phino>/resources
   PhiConfluence/RuleData.lean`; add `RuleConform.lean`. Compile and finish the one
   backward-direction puzzle.
2. Add the three modules to `PhiConfluence.lean`'s import list.
3. Add a CI job mirroring `rules-in-sync` for the data file
   (`gen-rule-data.py` → `git diff --exit-code PhiConfluence/RuleData.lean`); the
   deriver's fidelity lock means a phino change fails the regen step itself.
4. Add `PhiConfluence.conformance` and `PhiConfluence.rootStep_to_step` to the
   `#print axioms` gate in `build.yml` (expect `[propext, Quot.sound]` or cleaner).
5. Fix the display generator's `ξ` strip (`gen-rules.py`: `"xi"` → `"xi-free"`).

## Puzzles left

* **§M5-a** Complete the backward direction of `conformance` (see above).
* **§M5-b** Optional: extend the pin from `RootStep` to a statement about `Step`
  directly — e.g. prove `Step` is the compatible closure of `RootStep`, so the
  congruence constructors are visibly *not* phino-derived but the standard closure.
* **§M5-c** `λ`/`Δ` assets: the deriver has no rule for them by design (phino has
  none); if asset reduction is ever modelled, both the lock and the schema extend.
