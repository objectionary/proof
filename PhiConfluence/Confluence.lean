-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Abstract.Rewriting
import PhiConfluence.Diamond

/-!
# Confluence of φ-calculus normalization

**`confluence : WF e → e ↝∗ e₁ → e ↝∗ e₂ → ∃ e₃, e₁ ↝∗ e₃ ∧ e₂ ↝∗ e₃`** — the **headline**, the
`WF`-scoped Church-Rosser property and the README's theorem statement, covering every rule
`phino rewrite` applies, all twelve (the `⊥`-collapse rules
`dd/dc/null/over/stop/norho/miss/dl` + `stay` + `skip` + `dot` + `copy`, with the full
congruence closure).

Proved through the **WF-relativized bridge**: `redMany_eq` turns
`↝∗` into `Par∗`, `redMany_par_to_parWF` lifts the well-formed forks to `ParWF∗` (`ParWF` from
`Diamond.lean`), `parWF_confluent` joins them (the generic `Abstract.Diamond.confluent` =
`church_rosser`), and `parWF_to_par` + `redMany_eq` carry the join back. The `WF e` hypothesis
re-imposes the paper's own unique-key rule our looser `Binding` drops: it is *faithfulness*
(Def. Binding + `lookup`-vs-matcher agreement), carried but unused by the diamond.
See README "Why only well-formed terms". (The paper itself proves no confluence theorem; it *presupposes*
it when defining `≡` as "normal forms are syntactically identical" — we prove it.)

The paper's `λ`/`Δ` semantics (its *separate*, stateful Morphing/Dataization partial functions,
`fig:morphing`/`fig:dataization`) are outside the normalization relation `⟶` — hence outside this
theorem by construction, not pending work.
-/

namespace PhiConfluence

open PhiConfluence.Abstract

/-- Well-formedness is preserved along a whole `Par∗` chain (iterate `WF.par`). -/
theorem wf_redMany_par {a b : Term} (hwf : WF a) (h : Relation.ReflTransGen Par a b) : WF b := by
  induction h with
  | refl => exact hwf
  | tail _ hbc ih => exact WF.par ih hbc

/-- A `Par∗` chain out of a well-formed term is a `ParWF∗` chain: each step's source is well-formed
by `wf_redMany_par`, so it qualifies as a `ParWF` step. -/
theorem redMany_par_to_parWF {a b : Term} (hwf : WF a)
    (h : Relation.ReflTransGen Par a b) : Relation.ReflTransGen ParWF a b := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail ⟨wf_redMany_par hwf hab, hbc⟩

/-- `ParWF∗ ⊆ Par∗` (forget the `WF` tag on each step). -/
theorem parWF_to_par {a b : Term} (h : Relation.ReflTransGen ParWF a b) :
    Relation.ReflTransGen Par a b := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail hbc.2

/-- **The headline — confluence (Church-Rosser) of well-formed φ-terms.** For every well-formed
`e`, any fork `e ↝∗ e₁`, `e ↝∗ e₂` rejoins at some `e₃`. Proved via the WF-relativized diamond:
`redMany_eq` turns `↝∗` into `Par∗`, `redMany_par_to_parWF` lifts the well-formed forks to
`ParWF∗`, `parWF_confluent` joins them, and `parWF_to_par`+`redMany_eq` carry the join back to `↝∗`.

It governs every rule `phino rewrite` applies (the `⊥`-collapse rules + `stay` + `skip` + `dot` +
`copy`). The `WF e` hypothesis is faithfulness (Def. Binding + `lookup` agreement), carried but
unused by the diamond. The paper presupposes confluence (in its `≡`) but never proves it; we do. -/
theorem confluence {e e₁ e₂ : Term} (hwf : WF e)
    (h₁ : e ↝∗ e₁) (h₂ : e ↝∗ e₂) : ∃ e₃, e₁ ↝∗ e₃ ∧ e₂ ↝∗ e₃ := by
  rw [redMany_eq] at h₁ h₂
  obtain ⟨d, hd₁, hd₂⟩ :=
    parWF_confluent e e₁ e₂ (redMany_par_to_parWF hwf h₁) (redMany_par_to_parWF hwf h₂)
  exact ⟨d, by rw [redMany_eq]; exact parWF_to_par hd₁,
            by rw [redMany_eq]; exact parWF_to_par hd₂⟩

end PhiConfluence
