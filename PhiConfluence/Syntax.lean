-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

/-!
# Syntax of φ-calculus terms

The term language (Fig. 1 of the paper) with **named** attributes. `Term` and
`Binding` are mutually inductive because a formation `⟦B⟧` holds bindings whose
values are terms.

Encoding of the special forms: `Term.bot` is `⊥`, `Term.glob` is `Φ`, `Term.xi` is
the scope locator `ξ`, `Binding.void` is `τ↦∅`, `Binding.attached` is `τ↦e`,
`Binding.delta` is the `Δ`-asset (data), `Binding.lambda` is the `λ`-asset
(function). Assets (`Δ`/`λ`) are present in the syntax but **excluded from the
first confluence theorem**.

This is the M0 starting proposal — open to refinement (e.g. a unique-key `Record`
for bindings as in `objectionary/proof` `Minimal/Record.lean`, well-formedness of
formations, and the canonical `B₁,τ,B₂` splitting used by `dot`/`copy`/`null`).
-/

namespace PhiConfluence

/-- An attribute: `φ`, `ρ`, a positional `αᵢ`, or an ordinary label. -/
inductive Attr where
  | phi
  | rho
  | alpha (idx : Nat)
  | label (name : String)
deriving DecidableEq, Repr

mutual

/-- A φ-calculus expression. -/
inductive Term where
  | bot
  | glob
  | xi
  | form (bindings : List Binding)
  | dispatch (subject : Term) (attr : Attr)
  | app (subject : Term) (attr : Attr) (arg : Term)

/-- A single binding inside a formation `⟦…⟧`. -/
inductive Binding where
  | void (attr : Attr)
  | attached (attr : Attr) (value : Term)
  | delta (bytes : List UInt8)
  | lambda (fn : String)

end

end PhiConfluence
