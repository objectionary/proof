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
position (`⟦B₁, τ↦…, B₂⟧`) since no duplicate can shadow it. We will carry this
unique-key invariant as a hypothesis (or a `Record`-style indexed type) once the
formation-rebuilding rules arrive; for the current `⊥`-collapse fragment nothing
depends on it.
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

/-- The key of the binding at **domain ordinal** `i` — counting only non-asset attributes
(`Δ`/`λ` assets are skipped) — if that binding is `void`; otherwise `none`. This is `alpha`'s
positional index *over the domain* (paper Def. Ordinal; phino #749), **not** the raw list
position: `αᵢ` renames to the key of the `i`-th non-asset void slot. -/
def voidAtOrdinal : List Binding → Nat → Option Attr
  | [], _ => none
  | Binding.delta _ :: r, i => voidAtOrdinal r i
  | Binding.lambda _ :: r, i => voidAtOrdinal r i
  | Binding.void a :: _, 0 => some a
  | Binding.attached _ _ :: _, 0 => none
  | Binding.void _ :: r, i + 1 => voidAtOrdinal r i
  | Binding.attached _ _ :: r, i + 1 => voidAtOrdinal r i

end PhiConfluence
