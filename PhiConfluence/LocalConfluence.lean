-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Normal

/-!
# Reduction congruence-lifting helpers

Lemmas that lift multi-step reduction `↝∗` through each recursive `Term` position (a
dispatch subject, an application subject/argument, and a formation binding's value), plus
the inversion `form_step_inv` (the only way a formation steps is `congForm`). They feed the
parallel-reduction layer (`Parallel.lean`'s `par_to_red`, `redMany_form_cons`, etc.).

History: this module also held `local_confluence` — weak Church-Rosser of the `⊥`-collapse
fragment — proved at M1. It was **retired at M4.2b**: once `alpha` joins `Step`, unconditional
WCR is *false* (the `alpha`-vs-`over` fork on a malformed `αᵢ`-keyed formation is non-joinable,
dev. #8), and the headline `confluence` (via the parallel-reduction diamond, `Diamond.lean`/
`Confluence.lean`) subsumes local confluence anyway. The helper lemmas it relied on
(`cong_commute`, `lookup_set_*`, `hasLambda_set`) went with it; only the reduction-lifting
lemmas below — used elsewhere — remain.
-/

namespace PhiConfluence

open Relation

/-- Multi-step reduction lifts through a dispatch's subject. -/
theorem redMany_congDispatch {e e' : Term} (a : Attr) (h : e ↝∗ e') :
    (Term.dispatch e a) ↝∗ (Term.dispatch e' a) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.congDispatch step)

/-- Multi-step reduction lifts through an application's subject. -/
theorem redMany_congAppFn {e e' : Term} (a : Attr) (arg : Term) (h : e ↝∗ e') :
    (Term.app e a arg) ↝∗ (Term.app e' a arg) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.congAppFn step)

/-- Multi-step reduction lifts through an application's argument. -/
theorem redMany_congAppArg (e : Term) (a : Attr) {arg arg' : Term} (h : arg ↝∗ arg') :
    (Term.app e a arg) ↝∗ (Term.app e a arg') := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.congAppArg step)

/-- Multi-step reduction lifts through a formation binding's value. -/
theorem redMany_congForm {bs₁ bs₂ : List Binding} {a : Attr} {e e' : Term}
    (h : e ↝∗ e') :
    (Term.form (bs₁ ++ .attached a e :: bs₂)) ↝∗ (Term.form (bs₁ ++ .attached a e' :: bs₂)) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.congForm step)

/-- Inversion: the only way a formation steps is `congForm` (reducing one attached
binding's value). Stated with the list as a variable so `cases` can eliminate it — the
caller then gets the decomposition as data, sidestepping dependent elimination on an
append index. -/
theorem form_step_inv {L : List Binding} {b : Term} (h : Step (.form L) b) :
    ∃ (cs₁ : List Binding) (c : Attr) (f f' : Term) (cs₂ : List Binding),
      L = cs₁ ++ .attached c f :: cs₂ ∧ b = .form (cs₁ ++ .attached c f' :: cs₂) ∧ f ↝ f' := by
  cases h with
  | congForm st => exact ⟨_, _, _, _, _, rfl, rfl, st⟩

end PhiConfluence
