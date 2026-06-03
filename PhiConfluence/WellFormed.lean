-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Syntax

/-!
# Well-formed formations

The confluence theorem is stated for **well-formed** terms. A formation is well-formed
when its attribute `domain` (the keys, with `Δ`/`λ` assets excluded — paper Def. Domain,
`foundations.tex`) has **no duplicates** (Def. Binding "all keys are unique", M0-spec
deviation #6) and **every key is legal** — i.e. not a positional `αᵢ` (the paper grammar
puts `αᵢ` solely in application-argument pairs, M0-spec deviation #8). Both invariants
are load-bearing now that `alpha`/`dot`/`copy` are in `Step`: without deviation #8,
`alpha` vs `over` is a non-joinable critical pair.

`WF`/`WFB` are a **recursive `Prop` predicate** carried as a *hypothesis* on the diamond
and headline theorems — not an indexed `Binding` type (which would force re-deriving all
of `Syntax`/`Step`/`Attributes`/`LocalConfluence`). Its preservation engine
`domain_append`/`domain_set` follows the same key-invariance idea used throughout: reducing a
binding's *value* never changes the `domain`, so `WF` survives reduction (`Preservation.lean`).

Scope note: `Nodup` is over `domain`, which **excludes** `Δ`/`λ` assets, so `WF` does not
forbid duplicate assets (e.g. `⟦λ↦F, λ↦G⟧` is `WF`). That is fine for this theorem
(`λ`/`Δ` assets are inert — they have no rule among the eleven, so they never fire) but is
a latent looseness to tighten if asset reduction is ever modelled.
-/

namespace PhiConfluence

/-- The attribute a binding keys on (`Δ`/`λ` assets have no attribute key). -/
def Binding.key? : Binding → Option Attr
  | .void a => some a
  | .attached a _ => some a
  | .delta _ => none
  | .lambda _ => none

/-- A legal formation key is anything but a positional `αᵢ` (deviation #8). -/
def Attr.legalKey : Attr → Bool
  | .alpha _ => false
  | _ => true

/-- The domain of a binding list: its attribute keys, assets excluded (paper Def. Domain). -/
def domain : List Binding → List Attr
  | [] => []
  | b :: r =>
    match b.key? with
    | some k => k :: domain r
    | none => domain r

mutual

/-- A term is well-formed: every formation has a duplicate-free, `αᵢ`-free domain and
well-formed binding values. -/
inductive WF : Term → Prop where
  | bot : WF .bot
  | glob : WF .glob
  | xi : WF .xi
  | form {bs : List Binding} :
      (domain bs).Nodup → (∀ a ∈ domain bs, a.legalKey = true) → WFB bs → WF (.form bs)
  | dispatch {e : Term} {a : Attr} : WF e → WF (.dispatch e a)
  | app {e arg : Term} {a : Attr} : WF e → WF arg → WF (.app e a arg)

/-- Every value attached in a binding list is well-formed. -/
inductive WFB : List Binding → Prop where
  | nil : WFB []
  | consVoid {a : Attr} {r : List Binding} : WFB r → WFB (.void a :: r)
  | consAttached {a : Attr} {v : Term} {r : List Binding} : WF v → WFB r → WFB (.attached a v :: r)
  | consDelta {d : List UInt8} {r : List Binding} : WFB r → WFB (.delta d :: r)
  | consLambda {f : String} {r : List Binding} : WFB r → WFB (.lambda f :: r)

end

/-- `domain` distributes over `++` (each binding contributes its key independently). -/
theorem domain_append (bs cs : List Binding) :
    domain (bs ++ cs) = domain bs ++ domain cs := by
  induction bs with
  | nil => rfl
  | cons b r ih => cases b <;> simp [domain, Binding.key?, ih]

/-- Reducing one attached binding's value leaves the `domain` unchanged (it reads only
keys): the engine behind `WF` preservation under reduction (`Preservation.lean`'s `wfb_set`). -/
theorem domain_set {bs₁ bs₂ : List Binding} {a : Attr} {e e' : Term} :
    domain (bs₁ ++ .attached a e :: bs₂) = domain (bs₁ ++ .attached a e' :: bs₂) := by
  simp only [domain_append, domain, Binding.key?]

end PhiConfluence
