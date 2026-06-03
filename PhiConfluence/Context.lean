-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Syntax

/-!
# Contextualization and scope

The contextualization total function `ℂ : 𝓔 × 𝓑 → 𝓔`, written `ℂ(e ⊳ b)`, defined by
induction **in the paper** (`sections/operators.tex`, Fig. "Contextualization by
induction", `\label{r:contextualize}`). The paper is the source of truth; phino's
`Builder.contextualize` is one interpretation of it, and here the two agree exactly. It
removes the scope locator `ξ` (replacing it by the receiving `b`), fixes `Φ` and `⊥`,
**stops at a formation boundary** (`ℂ(⟦B⟧ ⊳ b) → ⟦B⟧` untouched — `ξ` inside a nested
formation is a *different* scope), and otherwise recurses through a dispatch's subject
and an application's subject *and* bound argument. `dot`/`copy` use it to relocate a
dispatched/applied value into its new home (`dot` passes the enclosing formation as `b`;
`copy` passes `scope(e₁)`). Cross-checked against phino's single-step `dot` including the
formation-boundary case.

(The paper types the receiver `b` in `𝓑` — the objects/formations; we model it as a
`Term`, a harmless generalization since `b` is only ever a formation and the definition
treats it opaquely.) `contextualize` is total and structurally recursive by construction.
The load-bearing **"`C` commutes with reduction"** lemma — the one `Diamond` consumes —
is the next step here and lands with the `dot`/`copy` rules.

`scope(e)` (`ς`, defined in the paper `sections/foundations.tex`: the formation where
`e` stays, or the scope of the subject of the application where `e` is the argument) is
deliberately **not** modelled — it depends on `e`'s surrounding context, not on `e` alone.
Neither rule as landed needs it: `dot`'s receiver is the dispatched formation itself, and
`copy` is `ξ`-free, so `C(e₁ ⊳ scope) = e₁` (`contextualize_eq_self`, `Parallel.lean`) makes any
`scope` vacuous. `scope` is therefore absent from the model by design (M0-spec dev. #7).
-/

namespace PhiConfluence

/-- `contextualize e context` (`C(e ⊳ context)`): substitute the scope locator `ξ` by
`context`, leaving `Φ`/`⊥` fixed and **stopping at formation boundaries**, recursing
through dispatch subjects and application subjects/arguments. The six cases are exactly
the paper's Fig. "Contextualization by induction" (`operators.tex`); phino's
`Builder.contextualize` agrees. -/
def contextualize : Term → Term → Term
  | .glob,         _   => .glob
  | .xi,           ctx => ctx
  | .bot,          _   => .bot
  | .form bs,      _   => .form bs
  | .dispatch e a, ctx => .dispatch (contextualize e ctx) a
  | .app e a arg,  ctx => .app (contextualize e ctx) a (contextualize arg ctx)

end PhiConfluence
