-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence

open PhiConfluence Term Attr Binding

/-!
Emits, for each example, a tab-separated line `<input>\t<our normal form>`, where the
input is the bare expression, as `phino rewrite` reads it.
`.github/difftest.sh` feeds the input to `phino rewrite --normalize` and checks
phino's normal form matches ours — the behavioral pin between our reducer and phino.
Corpus exercises every rule `phino rewrite` applies (all sixteen but `dotg`, which needs the
whole-program universe; `alpha` included — phino parses our printed `α0`).

A formation has a parent `ρ` only when it declares one, as phino does: nothing injects a `ρ↦∅`.
The corpus includes non-`⊥` formation results that match phino exactly, such as `⟦⟧(ρ↦Φ)`
(`skip` drops the `ρ` a formation does not declare) and `⟦ρ↦∅⟧(ρ↦Φ)` (`copy` fills a declared one).
The remaining `⊥`-cases keep the trace bounded (`dot`'s `ρ`-feedback can diverge) and exercise
the collapse rules.
-/

/-- Example programs across every rule `phino rewrite` applies, matching phino on `⊥`-collapse
outcomes and on real formation results, including a `ρ` that is declared or not, positional
ordinals that skip `ρ`, and `dot`'s context without the dispatched binding. -/
def cases : List Term :=
  [ dispatch (form [void (label "x")]) (label "x"),                     -- Rnull → ⊥
    dispatch bot (label "x"),                                           -- Rdd → ⊥
    app bot (label "x") glob,                                           -- Rdc → ⊥
    app (form [attached (label "x") glob]) (label "x") xi,              -- Rover → ⊥
    app (form [attached (label "y") glob]) (label "x") glob,            -- Rmiss → ⊥
    dispatch (form [void (label "x")]) (label "y"),                     -- Rstop → ⊥
    dispatch (app (form [attached rho glob]) rho glob) (label "x"),     -- Rstay then Rstop → ⊥
    dispatch (form [void phi]) (label "y"),                             -- φ present, no rule fires: normal
    dispatch (app (form [void (label "x")]) (label "x") glob) (label "y"),  -- Rcopy then Rstop → ⊥
    dispatch (form [attached (label "x") bot]) (label "x"),             -- Rdot then Rdc → ⊥
    dispatch (form [attached (label "x") (dispatch bot (label "z"))]) (label "x"),  -- congForm interior (Rdd inside) → ⊥
    dispatch (dispatch bot (label "x")) (label "y"),                    -- cong + Rdd → ⊥
    -- non-⊥ formation results (match phino exactly):
    form [attached (label "x") glob],                                   -- value: already normal
    app (form [attached rho glob]) rho glob,                            -- Rstay → ⟦ρ↦Φ⟧ (ρ explicit)
    app (form []) rho glob,                                             -- Rskip drops an undeclared ρ → ⟦⟧
    app (form [attached (label "x") glob]) rho glob,                    -- Rskip, not Rmiss → ⟦x↦Φ⟧
    app (form [void rho]) rho glob,                                     -- Rcopy fills a declared ρ → ⟦ρ↦Φ⟧
    app (form [void (label "x")]) (alpha 0) glob,                       -- Ralpha→x, Rcopy → ⟦x↦Φ⟧
    app (form [void (label "x")]) (alpha 1) glob,                       -- Ramiss: ordinals skip ρ → ⊥
    app (form [attached (label "x") glob]) (alpha 0) glob,              -- Rovera: α0 is attached → ⊥
    -- alpha indexes over the DOMAIN (skips the λ asset):
    app (form [lambda "Fn", void (label "x")]) (alpha 0) glob,          -- α0 skips λ, hits x → ⟦λ↦Fn, x↦Φ⟧
    app (form [lambda "Fn", void (label "x")]) (alpha 1) glob,          -- α1 past the domain (Ramiss) → ⊥
    -- a formation with both λ and Δ collapses (Rdl), even under a dispatch:
    form [lambda "Fn", delta [1]],                                      -- Rdl → ⊥
    dispatch (form [attached (label "x") (dispatch glob (label "y")), lambda "Fn", delta [0]])
      (label "x"),                                                      -- Rdl, Rdd → ⊥ (not Rdot)
    app (form [void (label "x")]) (label "x") bot,                      -- Rcopy of ⊥ → ⟦x↦⊥⟧
    -- dot contextualizes against the formation without the dispatched binding:
    dispatch (form [attached (label "x") xi]) (label "x"),              -- Rdot, Rskip → ⟦⟧
    dispatch (form [attached rho xi]) rho,                              -- Rdot, Rskip → ⟦⟧
    dispatch (form [void rho, attached (label "x") xi]) (label "x"),    -- Rdot, Rcopy → ⟦ρ↦⟦ρ↦∅, x↦ξ⟧⟧
    app (form [void rho, void (label "x")]) (alpha 0) glob,             -- ordinals skip ρ: α0 is x → ⟦ρ↦∅, x↦Φ⟧
    form [attached rho (form [])] ]                                     -- nothing adds ρ → ⟦ρ↦⟦⟧⟧

/-- Our reducer's normal form (bounded). -/
def normalForm (e : Term) : Term := (trace 100 e).getLastD e

def main : IO Unit := do
  for e in cases do
    IO.println (ppTerm e ++ "\t" ++ ppTerm (normalForm e))
