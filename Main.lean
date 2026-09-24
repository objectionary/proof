-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence

open PhiConfluence Term Attr Binding

/-- Example φ-programs (encoded as `Term`s) to normalize for the demo. -/
def examples : List (String × Term) :=
  [ ("⊥ dispatched (Rdd)",            dispatch bot (label "x")),
    ("nested dispatch (cong + Rdd)",  dispatch (dispatch bot (label "x")) (label "y")),
    ("void attribute (Rnull)",        dispatch (form [void (label "x")]) (label "x")),
    ("missing attribute (Rmiss)",     app (form [attached phi xi]) (label "a") glob),
    ("already attached (Rover)",      app (form [attached (label "x") glob]) (label "x") xi),
    ("apply ρ, a no-op (Rstay)",      app (form [attached rho glob]) rho glob),
    ("apply an undeclared ρ (Rskip)", app (form [attached (label "x") glob]) rho glob),
    ("positional rename (Ralpha)",    dispatch (app (form [void (label "x")]) (alpha 0) glob) (label "y")),
    ("positional overwrite (Rovera)", app (form [attached (label "x") glob]) (alpha 0) glob),
    ("positional overflow (Ramiss)",  app (form [void (label "x")]) (alpha 1) glob),
    ("atom with data (Rdl)",          dispatch (form [lambda "Fn", delta [1]]) (label "x")),
    ("fill a void slot (Rcopy)",      dispatch (app (form [void (label "x")]) (label "x") glob) (label "y")),
    ("ρ-feedback dispatch (Rdot)",    dispatch (form [attached (label "x") bot]) (label "x")),
    ("decorator dispatch (normal)",   dispatch (form [void phi]) (label "y")),
    ("normal form (no rule)",         dispatch glob (label "x")) ]

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println " φ-calculus normalization rules"
  IO.println " (generated from phino's resources/normalize/*.yaml — the SAME source the"
  IO.println "  paper's Fig. 4 is rendered from; compare directly)"
  IO.println "═══════════════════════════════════════════════════════════════"
  for r in normalizationRules do
    IO.println s!"  {ppRule r}"
  IO.println "  + congruence: a step may occur inside any subterm"
  IO.println ""
  IO.println " (The reducer below implements every rule `phino rewrite` applies — dd, dc/dca,"
  IO.println "  null, over, stop, miss, stay, skip, alpha, overa, amiss, dot, copy, dl; dotg needs the"
  IO.println "  whole-program universe and never fires — and `reduce_sound` proves every step it"
  IO.println "  takes is a genuine `Step`.)"
  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println " Example reductions, computed by this prover's own reducer"
  IO.println "═══════════════════════════════════════════════════════════════"
  for (name, e) in examples do
    let steps := trace 100 e
    IO.println s!"  {name}:"
    IO.println s!"    {String.intercalate "  ↝  " (steps.map ppTerm)}"
  IO.println ""
  IO.println " (Each printed step is produced by `reduceStep`, and `reduce_sound` proves"
  IO.println "  every such step is a genuine `Step` — so the trace is certified.)"
