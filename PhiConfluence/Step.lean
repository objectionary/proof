-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Syntax
import PhiConfluence.Attributes
import PhiConfluence.Nf
import PhiConfluence.Context
import Mathlib.Logic.Relation

/-!
# Single-step reduction `Step`

The reduction relation, encoded as an inductive relation: each constructor is one
way a term may reduce in a single step. A value of type `Step e e'` is *evidence*
that `e` reduces to `e'`.

This is grown incrementally across M1. Implemented now (the `⊥`-collapse fragment,
which needs no contextualization or formation rebuilding):

* `dd`   `⊥.τ ↝ ⊥`
* `dc`   `⊥(τ↦e) ↝ ⊥`
* `null` `⟦…τ↦∅…⟧.τ ↝ ⊥`           (dispatch on a void attribute)
* `over` `⟦…τ↦e₁…⟧(τ↦e₂) ↝ ⊥`      (apply to an already-attached `τ≠ρ`)
* `stop` `⟦B⟧.τ ↝ ⊥`               (dispatch a missing `τ`, no `φ`/`λ` to delegate to)
* `miss` `⟦B⟧(τ↦e) ↝ ⊥`            (apply a missing non-positional `τ`)
* `stay` `⟦…ρ↦e₁…⟧(ρ↦e₂) ↝ ⟦…ρ↦e₁…⟧`   (applying `ρ` to a formation that already has `ρ`)
* `phi`  `⟦B⟧.τ ↝ ⟦B⟧.φ.τ`         (dispatch a missing `τ` through the decoration `φ`)
* `alpha` `⟦B₁,τ₁↦∅,B₂⟧(αᵢ↦e) ↝ ⟦B₁,τ₁↦∅,B₂⟧(τ₁↦e)`  (rename a positional `αᵢ` to the key `τ₁`
  of the binding at **domain ordinal** `i` — the `i`-th *non-asset* binding — when it is void, via
  `voidAtOrdinal bs i`; `Δ`/`λ` assets are skipped, matching the paper's Def. Ordinal and phino #749)
* `dot`  `⟦B₁,τ↦e₁,B₂⟧.τ ↝ (C(e₁ ⊳ ⟦…⟧))(ρ↦⟦…⟧)`, guard `nf e₁`  (dispatch on an *attached*
  slot whose value is normal: contextualize it against the formation, then re-decorate with
  `ρ`↦the formation — the `ρ`-feedback that makes the system non-terminating)
* `copy` `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) ↝ ⟦B₁,τ↦e₁,B₂⟧`, guards `ξFree e₁` then `nf e₁`  (apply to a *void*
  slot a `ξ`-free normal argument: drop it into the slot. Under `ξFree`, the paper's
  `contextualize(e₁, scope)` is provably the identity, so there is no `scope`/contextualization —
  a local slot-fill, matching the corrected paper + phino)

plus the congruence constructors that let a step happen *inside* a dispatch, an
application, or a formation binding (`congForm`, paper `B₁,τ↦e,B₂` splitting — reduction
may occur anywhere). **All eleven rules are now present.** With `alpha`/`dot`/`copy`, confluence is
**`WF`-scoped** (the `alpha`-vs-`over` fork on a malformed `αᵢ`-keyed formation is non-joinable; `WF`
bars it) and proved via the parallel diamond (non-termination ⇒ no Newman).
-/

namespace PhiConfluence

/-- One reduction step. Each constructor is a rule of the calculus. -/
inductive Step : Term → Term → Prop where
  | dd (a : Attr) :
      Step (.dispatch .bot a) .bot
  | dc (a : Attr) (e : Term) :
      Step (.app .bot a e) .bot
  | null {bs : List Binding} {a : Attr} :
      lookup bs a = .void → Step (.dispatch (.form bs) a) .bot
  | over {bs : List Binding} {a : Attr} {e₁ e₂ : Term} :
      lookup bs a = .attached e₁ → a ≠ .rho → Step (.app (.form bs) a e₂) .bot
  | stop {bs : List Binding} {a : Attr} :
      lookup bs a = .absent → lookup bs .phi = .absent → hasLambda bs = false →
      Step (.dispatch (.form bs) a) .bot
  | miss {bs : List Binding} {a : Attr} {e : Term} :
      lookup bs a = .absent → a.isAlpha = false → Step (.app (.form bs) a e) .bot
  | stay {bs : List Binding} {e₁ e₂ : Term} :
      lookup bs .rho = .attached e₁ → Step (.app (.form bs) .rho e₂) (.form bs)
  | phi {bs : List Binding} {a : Attr} :
      lookup bs .phi ≠ .absent → lookup bs a = .absent →
      Step (.dispatch (.form bs) a) (.dispatch (.dispatch (.form bs) .phi) a)
  | alpha {bs : List Binding} {i : Nat} {τ₁ : Attr} {e : Term} :
      voidAtOrdinal bs i = some τ₁ →
      Step (.app (.form bs) (.alpha i) e) (.app (.form bs) τ₁ e)
  | dot {bs : List Binding} {a : Attr} {e₁ : Term} :
      lookup bs a = .attached e₁ → nf e₁ = true →
      Step (.dispatch (.form bs) a) (.app (contextualize e₁ (.form bs)) .rho (.form bs))
  | copy {bs : List Binding} {a : Attr} {e₁ : Term} :
      lookup bs a = .void → xiFree e₁ = true → nf e₁ = true →
      Step (.app (.form bs) a e₁) (.form (fill bs a e₁))
  | congDispatch {e e' : Term} {a : Attr} :
      Step e e' → Step (.dispatch e a) (.dispatch e' a)
  | congAppFn {e e' : Term} {a : Attr} {arg : Term} :
      Step e e' → Step (.app e a arg) (.app e' a arg)
  | congAppArg {e : Term} {a : Attr} {arg arg' : Term} :
      Step arg arg' → Step (.app e a arg) (.app e a arg')
  | congForm {bs₁ bs₂ : List Binding} {a : Attr} {e e' : Term} :
      Step e e' →
      Step (.form (bs₁ ++ .attached a e :: bs₂)) (.form (bs₁ ++ .attached a e' :: bs₂))

/-- Notation `e ↝ e'` for a single reduction step. -/
infix:50 " ↝ " => Step

/-- Multi-step reduction: the reflexive-transitive closure of `Step`. -/
abbrev RedMany : Term → Term → Prop := Relation.ReflTransGen Step

/-- Notation `e ↝∗ e'` for zero or more reduction steps. -/
infix:50 " ↝∗ " => RedMany

end PhiConfluence
