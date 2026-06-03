-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Confluence

/-!
# Equivalence `≡`

The paper's `≡` ("two expressions are equivalent if their normal forms are syntactically
identical"). On a *non-terminating* system not every term has a normal form, so — following the
Church-Rosser tradition — we take `≡` to be **convertibility**, modelled as *having a common
reduct* (`Conv e₁ e₂ := ∃ d, e₁ ↝∗ d ∧ e₂ ↝∗ d`). It is reflexive and symmetric unconditionally;
**confluence** supplies transitivity, so `Conv` is an `Equivalence` relation on the well-formed
terms (the Church-Rosser corollary). The paper's literal "identical normal forms" is the special
case where both reducts are normal — and `Conv` agreeing with that on normalizing terms is exactly
what confluence guarantees (a normalizing term has a *unique* normal form).
-/

namespace PhiConfluence

/-- Convertibility: `e₁` and `e₂` reduce to a common term. (`Relation.Join` of `↝∗`.) -/
def Conv (e₁ e₂ : Term) : Prop := ∃ d, e₁ ↝∗ d ∧ e₂ ↝∗ d

/-- Convertibility is reflexive (a term reduces to itself). -/
theorem conv_refl (e : Term) : Conv e e := ⟨e, .refl, .refl⟩

/-- Convertibility is symmetric. -/
theorem conv_symm {e₁ e₂ : Term} (h : Conv e₁ e₂) : Conv e₂ e₁ :=
  let ⟨d, h₁, h₂⟩ := h; ⟨d, h₂, h₁⟩

/-- Convertibility is transitive **when the middle term is well-formed** — this is the one step
that needs `confluence` (the two reducts of the middle term must themselves rejoin). -/
theorem conv_trans {e₁ e₂ e₃ : Term} (hwf : WF e₂) (h₁₂ : Conv e₁ e₂) (h₂₃ : Conv e₂ e₃) :
    Conv e₁ e₃ := by
  obtain ⟨d₁, he₁, he₂⟩ := h₁₂
  obtain ⟨d₂, he₂', he₃⟩ := h₂₃
  obtain ⟨d, hd₁, hd₂⟩ := confluence hwf he₂ he₂'
  exact ⟨d, he₁.trans hd₁, he₃.trans hd₂⟩

/-- **The Church-Rosser corollary:** convertibility is an `Equivalence` relation on the well-formed
terms `{e // WF e}`. Reflexivity and symmetry are free; transitivity is `conv_trans`, whose use of
`confluence` is exactly why the system must be confluent for `≡` to be well-behaved. -/
theorem conv_equivalence : Equivalence (fun a b : {e : Term // WF e} => Conv a.1 b.1) where
  refl a := conv_refl a.1
  symm h := conv_symm h
  trans {_a b _} h₁ h₂ := conv_trans b.2 h₁ h₂

end PhiConfluence
