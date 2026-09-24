-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Step
import Mathlib.Tactic

/-!
# Reducibility and normal forms

A term is `Reducible` if some single step applies to it, and a `NormalForm` if no
step applies. The `nf`-guarded rules `dot`/`copy` use the *structural* `nf` instead
(`Nf.lean`, mirroring `phino`'s `isNF`); `nf_iff` (`Parallel.lean`) proves the two agree on
well-formed terms.
-/

namespace PhiConfluence

/-- A term is reducible if it can take at least one step. -/
def Reducible (e : Term) : Prop := ∃ e', e ↝ e'

/-- A normal form is an irreducible term. -/
def NormalForm (e : Term) : Prop := ¬ Reducible e

/-- The terminator `⊥` is a normal form: no rule reduces it. -/
theorem bot_normalForm : NormalForm Term.bot := by
  rintro ⟨e', step⟩
  cases step

/-- The global root `Φ` is a normal form. -/
theorem glob_normalForm : NormalForm Term.glob := by
  rintro ⟨e', step⟩
  cases step

/-- Applying anything to `⊥` reduces (in one step, hence many) to `⊥`. -/
theorem bot_app_redMany (a : Attr) (e : Term) : (Term.app Term.bot a e) ↝∗ Term.bot :=
  Relation.ReflTransGen.single (Step.dc a e)

/-- Dispatching off `⊥` reduces (in one step, hence many) to `⊥`. -/
theorem bot_dispatch_redMany (a : Attr) : (Term.dispatch Term.bot a) ↝∗ Term.bot :=
  Relation.ReflTransGen.single (Step.dd a)

/-- `⊥` is a sink: anything reachable from `⊥` is `⊥` itself. -/
theorem redMany_bot {e : Term} (h : Term.bot ↝∗ e) : e = Term.bot := by
  induction h with
  | refl => rfl
  | tail _ step ih => subst ih; cases step

end PhiConfluence
