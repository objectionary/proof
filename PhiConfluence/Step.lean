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
that `e` reduces to `e'`. The constructors transcribe phino 0.0.138's
`resources/normalize/*.yaml`:

* `dd`    `⊥.τ ↝ ⊥`
* `dc`    `⊥(τ↦e) ↝ ⊥`, for any attribute, so it also covers phino's positional `dca`
* `null`  `⟦…τ↦∅…⟧.τ ↝ ⊥`
* `over`  `⟦…τ↦e₁…⟧(τ↦e₂) ↝ ⊥`, guard `τ ≠ ρ`
* `stop`  `⟦B⟧.τ ↝ ⊥`, guards `τ ∉ B`, `φ ∉ B`, `λ ∉ B`
* `miss`  `⟦B⟧(τ↦e) ↝ ⊥`, guard `τ ∉ B`; in phino `τ` never matches a positional `αᵢ`,
  which `a.isAlpha = false` spells out here
* `stay`  `⟦…ρ↦e₁…⟧(ρ↦e₂) ↝ ⟦…ρ↦e₁…⟧`
* `alpha` `⟦B⟧(αᵢ↦e) ↝ ⟦B⟧(τ↦e)` when the binding at domain ordinal `i` is the void `τ`
  (`ordinal` skips `Δ`/`λ` assets and `ρ`, as phino's `domain` does)
* `overa` `⟦B⟧(αᵢ↦e) ↝ ⊥` when the binding at domain ordinal `i` is attached
* `amiss` `⟦B⟧(αᵢ↦e) ↝ ⊥` when the domain has no ordinal `i`
* `dot`   `⟦B₁,τ↦e₁,B₂⟧.τ ↝ (C(e₁ ⊳ ⟦B₁,B₂⟧))(ρ↦⟦B₁,τ↦e₁,B₂⟧)`, guards `nf e₁` and
  "not both `λ` and `Δ`"; the context drops the dispatched binding (`erase`) and, as
  phino's builder does, gains a `ρ↦∅` when that binding was `ρ` (`ensureRho`)
* `copy`  `⟦B₁,τ↦∅,B₂⟧(τ↦e₁) ↝ ⟦B₁,τ↦e₁,B₂⟧`, guards `ξFree e₁` and `nf e₁` (phino's `𝑘`)
* `dl`    `⟦B⟧ ↝ ⊥` when `B` holds both a `λ` and a `Δ` asset

plus the congruence constructors that let a step happen inside a dispatch, an
application, or a formation binding. phino's `dotg` is absent on purpose: it fires only
when the dispatched formation is the whole program, a universe that `phino rewrite`
never knows, so there `dot` answers every dispatch, and so does `Step`.
Confluence is `WF`-scoped (a positional `αᵢ` used as a key makes `alpha` and `copy`
disagree; `WF` bars it) and proved via the parallel diamond (non-termination ⇒ no Newman).
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
  | alpha {bs : List Binding} {i : Nat} {τ₁ : Attr} {e : Term} :
      ordinal bs i = some τ₁ → lookup bs τ₁ = .void →
      Step (.app (.form bs) (.alpha i) e) (.app (.form bs) τ₁ e)
  | overa {bs : List Binding} {i : Nat} {τ₁ : Attr} {e₁ e : Term} :
      ordinal bs i = some τ₁ → lookup bs τ₁ = .attached e₁ →
      Step (.app (.form bs) (.alpha i) e) .bot
  | amiss {bs : List Binding} {i : Nat} {e : Term} :
      ordinal bs i = none → Step (.app (.form bs) (.alpha i) e) .bot
  | dot {bs : List Binding} {a : Attr} {e₁ : Term} :
      lookup bs a = .attached e₁ → nf e₁ = true → (hasLambda bs && hasDelta bs) = false →
      Step (.dispatch (.form bs) a)
        (.app (contextualize e₁ (.form (ensureRho (erase bs a)))) .rho (.form bs))
  | copy {bs : List Binding} {a : Attr} {e₁ : Term} :
      lookup bs a = .void → xiFree e₁ = true → nf e₁ = true →
      Step (.app (.form bs) a e₁) (.form (fill bs a e₁))
  | dl {bs : List Binding} :
      hasLambda bs = true → hasDelta bs = true → Step (.form bs) .bot
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
