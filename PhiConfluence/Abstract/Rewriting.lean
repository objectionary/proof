-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import Mathlib.Logic.Relation

/-!
# Abstract rewriting systems

Calculus-independent confluence vocabulary, built on mathlib's `Relation` API.

`Relation.ReflTransGen r` is the reflexive-transitive closure of a step relation
`r` (zero-or-more steps), written `r∗`. `Relation.Join r a b` says `a` and `b` have
a common `r`-reduct. We name two properties on top of these:

* `Diamond r` — a one-step fork rejoins in one step on each side.
* `Confluent r` — a many-step fork rejoins in many steps (the Church-Rosser
  property of `ReflTransGen r`).

The bridge `Diamond.confluent` derives confluence of the closure from a single-step
diamond, with NO termination assumption, by discharging mathlib's
`Relation.church_rosser`. The φ-calculus proof gives the diamond for *parallel
reduction* and feeds it here.

We use mathlib's `Prop`-valued relations (the idiomatic choice) rather than the
`Type`-valued library of `objectionary/proof`'s `Minimal/ARS.lean`; we keep that
older file only as a proof-skeleton reference.
-/

namespace PhiConfluence.Abstract

open Relation

variable {α : Type*} {r : α → α → Prop}

/-- One-step fork rejoins in one step on each side. -/
def Diamond (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d

/-- Many-step fork rejoins in many steps: the Church-Rosser property of `r∗`. -/
def Confluent (r : α → α → Prop) : Prop :=
  ∀ a b c, ReflTransGen r a b → ReflTransGen r a c → Join (ReflTransGen r) b c

/-- A relation with the diamond property is confluent (no termination needed). -/
theorem Diamond.confluent (h : Diamond r) : Confluent r := by
  intro a b c hab hac
  refine church_rosser ?strong hab hac
  case strong =>
    intro x y z hxy hxz
    obtain ⟨d, hyd, hzd⟩ := h x y z hxy hxz
    exact ⟨d, ReflGen.single hyd, ReflTransGen.single hzd⟩

end PhiConfluence.Abstract
