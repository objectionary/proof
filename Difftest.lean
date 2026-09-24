-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence

open PhiConfluence Term Attr Binding

/-!
Emits, for each example, a tab-separated line `<input>\t<our normal form>`, where the
input is the bare expression, as `phino rewrite` reads it.
`.github/difftest.sh` feeds the input to `phino rewrite --normalize` and checks
phino's normal form matches ours — the behavioral pin between our reducer and phino.
Corpus exercises every rule `phino rewrite` applies (all fifteen but `dotg`, which needs the
whole-program universe; `alpha` included — phino parses our printed `α0`).

**The implicit parent (`ρ`) is now modelled — `canon`.** The paper (`foundations.tex`, Def. Parent)
and phino put a parent `ρ`, void until set, in *every* formation; phino materialises it as a `ρ↦∅`
appended where absent. `normalForm` below first applies `canon` (`PhiConfluence.canon`) — exactly
that injection — so our reducer runs on phino's term space. This **closes the former `ρ`-injection
gap**: the corpus now includes **non-`⊥` formation results that match phino exactly**, including the
cases that previously diverged — `⟦⟧(ρ↦Φ)` (phino fills the implicit `ρ` via `copy`) and bare
value formations
(`⟦x↦Φ⟧ ↦ ⟦x↦Φ, ρ↦∅⟧`). The remaining `⊥`-cases keep the trace bounded (`dot`'s `ρ`-feedback can
diverge) and exercise the collapse rules. `canon`'s correctness is proved: `canon_canonical`
(every formation gets a `ρ`), `wf_canon` (`WF` preserved), `step_canonical` (reduction stays
canonical — phino's term space is closed under `Step`).
-/

/-- Example programs across every rule `phino rewrite` applies. After `canon` (parent injection) our
reducer matches phino on `⊥`-collapse outcomes *and* on real formation results — including
`⟦⟧(ρ↦Φ)`, positional ordinals that skip the implicit `ρ`, and `dot`'s context without the
dispatched binding. -/
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
    -- non-⊥ formation results (parent modelled by `canon`; match phino exactly):
    form [attached (label "x") glob],                                   -- value: → ⟦x↦Φ, ρ↦∅⟧ (canon adds ρ)
    app (form [attached rho glob]) rho glob,                            -- Rstay → ⟦ρ↦Φ⟧ (ρ explicit)
    app (form []) rho glob,                                             -- Rcopy fills implicit ρ → ⟦ρ↦Φ⟧
    app (form [void (label "x")]) (alpha 0) glob,                       -- Ralpha→x, Rcopy → ⟦x↦Φ, ρ↦∅⟧
    app (form [void (label "x")]) (alpha 1) glob,                       -- Ramiss: ordinals skip ρ → ⊥
    app (form [attached (label "x") glob]) (alpha 0) glob,              -- Rovera: α0 is attached → ⊥
    -- alpha indexes over the DOMAIN (skips the λ asset; phino #749):
    app (form [lambda "Fn", void (label "x")]) (alpha 0) glob,          -- α0 skips λ, hits x → ⟦λ↦Fn, x↦Φ, ρ↦∅⟧
    app (form [lambda "Fn", void (label "x")]) (alpha 1) glob,          -- α1 past the domain (Ramiss) → ⊥
    -- a formation with both λ and Δ collapses (Rdl), even under a dispatch (phino #1395):
    form [lambda "Fn", delta [1]],                                      -- Rdl → ⊥
    dispatch (form [attached (label "x") (dispatch glob (label "y")), lambda "Fn", delta [0]])
      (label "x"),                                                      -- Rdl, Rdd → ⊥ (not Rdot)
    app (form [void (label "x")]) (label "x") bot,                      -- Rcopy of ⊥ → ⟦x↦⊥, ρ↦∅⟧
    -- dot contextualizes against the formation without the dispatched binding:
    dispatch (form [attached (label "x") xi]) (label "x"),              -- Rdot, Rcopy → ⟦ρ↦⟦x↦ξ, ρ↦∅⟧⟧
    dispatch (form [attached rho xi]) rho,                              -- Rdot, Rcopy → ⟦ρ↦⟦ρ↦ξ⟧⟧
    form [attached rho (form [])] ]                                     -- parent: single ρ, no dup (phino #748) → ⟦ρ↦⟦ρ↦∅⟧⟧

/-- Our reducer's normal form (bounded), on the **canonicalised** term — `canon` injects the implicit
parent `ρ` exactly as phino does, so the result matches phino's normal form. -/
def normalForm (e : Term) : Term := let c := canon e; (trace 100 c).getLastD c

def main : IO Unit := do
  for e in cases do
    IO.println (ppTerm e ++ "\t" ++ ppTerm (normalForm e))
