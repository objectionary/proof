-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Syntax

/-!
# Attribute lookup over formations

The rule side conditions query a formation's bindings: is an attribute absent,
void (`τ↦∅`), or attached to a value (`τ↦e`)? `lookup` answers that by walking the
binding list (first match wins; the `Δ`/`λ` assets are skipped, since they are not
ordinary attributes). `DecidableEq Attr` (derived in `Syntax`) makes the `=` test
computable.

Well-formedness assumption: by the paper's Def. 4.8 a binding is "a sequence of
key-value pairs, where all keys are unique." Under that invariant, `lookup`'s
first-match-wins coincides with `phino`'s matcher, which can match a binding at any
position (`⟦B₁, τ↦…, B₂⟧`) since no duplicate can shadow it. The invariant is the
`Nodup` clause of `WF` (`WellFormed.lean`), carried as a hypothesis by the headline.
-/

namespace PhiConfluence

/-- The three outcomes of looking an attribute up in a formation. -/
inductive LookupResult where
  | absent
  | void
  | attached (value : Term)

/-- Look an attribute up in a binding list; assets (`Δ`, `λ`) are skipped. -/
def lookup : List Binding → Attr → LookupResult
  | [], _ => .absent
  | Binding.void a :: rest, t => if a = t then .void else lookup rest t
  | Binding.attached a v :: rest, t => if a = t then .attached v else lookup rest t
  | Binding.delta _ :: rest, t => lookup rest t
  | Binding.lambda _ :: rest, t => lookup rest t

/-- Does the formation carry a `λ`-asset (is it an atom)? -/
def hasLambda : List Binding → Bool
  | [] => false
  | Binding.lambda _ :: _ => true
  | _ :: rest => hasLambda rest

/-- Is the attribute a positional `αᵢ`? -/
def Attr.isAlpha : Attr → Bool
  | .alpha _ => true
  | _ => false

/-- Replace the first binding keyed on `a` (void or attached) by `a ↦ e` — the local `copy`
slot-fill (structural, first-match like `lookup`). `copy` fires on a `void` slot, turning that
`void a` into `attached a e`. -/
def fill : List Binding → Attr → Term → List Binding
  | [], _, _ => []
  | Binding.void c :: r, a, e => if c = a then Binding.attached a e :: r else Binding.void c :: fill r a e
  | Binding.attached c v :: r, a, e => if c = a then Binding.attached c v :: r else Binding.attached c v :: fill r a e
  | Binding.delta d :: r, a, e => Binding.delta d :: fill r a e
  | Binding.lambda f :: r, a, e => Binding.lambda f :: fill r a e

/-- Does the formation carry a `Δ`-asset (is it data)? -/
def hasDelta : List Binding → Bool
  | [] => false
  | Binding.delta _ :: _ => true
  | _ :: rest => hasDelta rest

/-- The key of the binding at **domain ordinal** `i`, counting only the bindings phino's
`domain` counts: `Δ`/`λ` assets and `ρ` are skipped. This is the positional index that
`alpha`, `overa` and `amiss` read, **not** the raw list position; `none` when the domain
is shorter than `i + 1`. -/
def ordinal : List Binding → Nat → Option Attr
  | [], _ => none
  | Binding.delta _ :: r, i => ordinal r i
  | Binding.lambda _ :: r, i => ordinal r i
  | Binding.void a :: r, i =>
      if a = .rho then ordinal r i else match i with | 0 => some a | j + 1 => ordinal r j
  | Binding.attached a _ :: r, i =>
      if a = .rho then ordinal r i else match i with | 0 => some a | j + 1 => ordinal r j

/-- Drop the first binding keyed on `a` (void or attached) — the `⟦B₁, B₂⟧` that `dot`
contextualizes against, the formation without the dispatched binding. -/
def erase : List Binding → Attr → List Binding
  | [], _ => []
  | Binding.void c :: r, a => if c = a then r else Binding.void c :: erase r a
  | Binding.attached c v :: r, a => if c = a then r else Binding.attached c v :: erase r a
  | Binding.delta d :: r, a => Binding.delta d :: erase r a
  | Binding.lambda f :: r, a => Binding.lambda f :: erase r a

/-- Ensure a binding list carries a parent: append `ρ↦∅` at the end iff no `ρ` key is present
(phino's `withVoidRho`; explicit `ρ` is kept in place, never duplicated). -/
def ensureRho (bs : List Binding) : List Binding :=
  match lookup bs .rho with
  | .absent => bs ++ [.void .rho]
  | _       => bs

end PhiConfluence
