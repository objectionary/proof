-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Syntax

/-!
# Pretty-printing terms

Renders a `Term` in the paper's Unicode φ-notation (`⟦ ⟧`, `ξ`, `Φ`, `⊥`, `∅`,
`↦`, `Δ ⤍`, `λ ⤍`) so the demo executable can show reductions a reader can compare
directly with the paper. Display-only (`partial`), with no role in any proof.
-/

namespace PhiConfluence

/-- A normalization rule as displayable data (name, pattern, result, side
condition, and meta-function `where`-clause), generated from phino's YAML. -/
structure RuleSpec where
  name : String
  pattern : String
  result : String
  cond : String
  wher : String

/-- Render a rule in the paper's `R<name>  pattern ↝ result  if cond  where …` form. -/
def ppRule (r : RuleSpec) : String :=
  let label := s!"R{r.name}"
  let label := label ++ String.ofList (List.replicate (9 - label.length) ' ')
  let base := label ++ r.pattern ++ "  ↝  " ++ r.result
  let base := if r.cond == "" then base else base ++ "   if " ++ r.cond
  if r.wher == "" then base else base ++ "   where " ++ r.wher

/-- Render an attribute. -/
def ppAttr : Attr → String
  | .phi => "φ"
  | .rho => "ρ"
  | .alpha i => "α" ++ toString i
  | .label s => s

mutual

/-- Render a term in Unicode φ-notation. -/
partial def ppTerm : Term → String
  | .bot => "⊥"
  | .glob => "Φ"
  | .xi => "ξ"
  | .form bs => "⟦" ++ ppBindings bs ++ "⟧"
  | .dispatch e a => ppTerm e ++ "." ++ ppAttr a
  | .app e a arg => ppTerm e ++ "(" ++ ppAttr a ++ " ↦ " ++ ppTerm arg ++ ")"

/-- Render a comma-separated binding list. -/
partial def ppBindings : List Binding → String
  | [] => ""
  | [b] => ppBinding b
  | b :: rest => ppBinding b ++ ", " ++ ppBindings rest

/-- Render a single binding. -/
partial def ppBinding : Binding → String
  | .void a => ppAttr a ++ " ↦ ∅"
  | .attached a v => ppAttr a ++ " ↦ " ++ ppTerm v
  | .delta _ => "Δ ⤍ …"
  | .lambda fn => "λ ⤍ " ++ fn

end

end PhiConfluence
