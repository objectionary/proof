-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence

open PhiConfluence Term Attr Binding

/-!
Emits, for each example, a tab-separated line `<input>\t<our normal form>`, where the
input is wrapped as a phino program with the `{ e }` sugar (= `Φ ↦ e`).
`scripts/difftest.sh` feeds the input to `phino rewrite --normalize` and checks
phino's normal form matches ours — the behavioral pin between our reducer and phino.
Corpus exercises **all eleven** rules (`alpha` included — phino parses our printed `α0`).

**The implicit parent (`ρ`) is now modelled — `canon`.** The paper (`foundations.tex`, Def. Parent)
and phino put a parent `ρ`, void until set, in *every* formation; phino materialises it as a `ρ↦∅`
appended where absent. `normalForm` below first applies `canon` (`PhiConfluence.canon`) — exactly
that injection — so our reducer runs on phino's term space. This **closes the former `ρ`-injection
gap**: the corpus now includes **non-`⊥` formation results that match phino exactly**, including the
cases that previously diverged — `⟦⟧(ρ↦Φ)` (phino fills the implicit `ρ` via `copy`), `⟦x↦∅⟧(α1↦Φ)`
(the index hits the implicit `ρ`; was *stuck* for us before `canon`), and bare value formations
(`⟦x↦Φ⟧ ↦ ⟦x↦Φ, ρ↦∅⟧`). The remaining `⊥`-cases keep the trace bounded (`dot`'s `ρ`-feedback can
diverge) and exercise the collapse rules. `canon`'s correctness is proved: `canon_canonical`
(every formation gets a `ρ`), `wf_canon` (`WF` preserved), `step_canonical` (reduction stays
canonical — phino's term space is closed under `Step`).
-/

/-- Example programs across all eleven rules. After `canon` (parent injection) our reducer matches
phino on `⊥`-collapse outcomes *and* on real formation results — including `⟦⟧(ρ↦Φ)` and the
`alpha`-to-implicit-`ρ` case that diverged before `canon`. -/
def cases : List Term :=
  [ dispatch (form [void (label "x")]) (label "x"),                     -- Rnull → ⊥
    dispatch bot (label "x"),                                           -- Rdd → ⊥
    app bot (label "x") glob,                                           -- Rdc → ⊥
    app (form [attached (label "x") glob]) (label "x") xi,              -- Rover → ⊥
    app (form [attached (label "y") glob]) (label "x") glob,            -- Rmiss → ⊥
    dispatch (form [void (label "x")]) (label "y"),                     -- Rstop → ⊥
    dispatch (app (form [attached rho glob]) rho glob) (label "x"),     -- Rstay then Rstop → ⊥
    dispatch (form [void phi]) (label "y"),                             -- Rphi then Rnull/Rdd → ⊥
    dispatch (app (form [void (label "x")]) (label "x") glob) (label "y"),  -- Rcopy then Rstop → ⊥
    dispatch (form [attached (label "x") bot]) (label "x"),             -- Rdot then Rdc → ⊥
    dispatch (form [attached (label "x") (dispatch bot (label "z"))]) (label "x"),  -- congForm interior (Rdd inside) → ⊥
    dispatch (dispatch bot (label "x")) (label "y"),                    -- cong + Rdd → ⊥
    -- non-⊥ formation results (parent modelled by `canon`; match phino exactly):
    form [attached (label "x") glob],                                   -- value: → ⟦x↦Φ, ρ↦∅⟧ (canon adds ρ)
    app (form [attached rho glob]) rho glob,                            -- Rstay → ⟦ρ↦Φ⟧ (ρ explicit)
    app (form []) rho glob,                                             -- Rcopy fills implicit ρ → ⟦ρ↦Φ⟧
    app (form [void (label "x")]) (alpha 0) glob,                       -- Ralpha→x, Rcopy → ⟦x↦Φ, ρ↦∅⟧
    app (form [void (label "x")]) (alpha 1) glob,                       -- Ralpha hits implicit ρ → ⟦x↦∅, ρ↦Φ⟧
    -- alpha indexes over the DOMAIN (skips the λ asset; phino #749):
    app (form [lambda "Fn", void (label "x")]) (alpha 0) glob,          -- α0 skips λ, hits x → ⟦λ↦Fn, x↦Φ, ρ↦∅⟧
    app (form [lambda "Fn", void (label "x")]) (alpha 1) glob,          -- α1 = 1st non-asset (ρ) → ⟦λ↦Fn, x↦∅, ρ↦Φ⟧
    form [attached rho (form [])] ]                                     -- parent: single ρ, no dup (phino #748) → ⟦ρ↦⟦ρ↦∅⟧⟧

/-- Our reducer's normal form (bounded), on the **canonicalised** term — `canon` injects the implicit
parent `ρ` exactly as phino does, so the result matches phino's normal form. -/
def normalForm (e : Term) : Term := let c := canon e; (trace 100 c).getLastD c

def main : IO Unit := do
  for e in cases do
    IO.println ("{ " ++ ppTerm e ++ " }\t" ++ ppTerm (normalForm e))
