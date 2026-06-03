-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Preservation
import PhiConfluence.Context
import PhiConfluence.Abstract.Rewriting

/-!
# The diamond property for parallel reduction

Two halves connect `Step` to confluence: (1) `step ⊆ ⇒ ⊆ step*`, so `ReflTransGen Step` and
`ReflTransGen (⇒)` coincide (`redMany_eq`, in `Parallel.lean`); (2) the **Takahashi triangle**
`par_triangle : WF e → Par e u → Par u (devel e)` (also in `Parallel.lean`), which collapses the
diamond to a single apex `devel e`.

**The WF-relativized diamond — the permanent headline path.** With `alpha` present the
*unconditional* diamond is FALSE (`alpha`-vs-`over` on malformed `αᵢ`-keyed formations, dev. #8),
but `church_rosser` demands an unconditional strong-confluence premise. The fix: relativize to
`ParWF a b := WF a ∧ Par a b` and prove `Diamond ParWF` — with `d := devel a`, any fork
`ParWF a b`, `ParWF a c` rejoins because the (now WF-scoped) triangle sends both `b` and `c` to
`devel a`; the targets stay `WF`-rooted by `WF.par`. Crucially `Diamond ParWF` needs `WF` of the
*source* `a` only (not of `devel a`), so it discharges the unconditional premise for the relation
`ParWF`. The SAME generic `Abstract.Diamond.confluent` then gives `Confluent ParWF`, which
`Confluence.lean` bridges to the `WF`-scoped headline `confluence`. As `dot`/`copy` land
(M4.3/4.4), only `par_triangle`/`devel`/`Step`/`Par` change, not this plumbing. (De-risked: no
root critical pairs, no divergence over a fixed corpus of 7 hand-crafted probe programs + the
paper's Appendix-A examples — `docs/DESIGN.md` §7; a fixed corpus, not random fuzzing.) There is
deliberately no unconditional `par_diamond`/`step_confluent` now — they would be false.
-/

namespace PhiConfluence

open PhiConfluence.Abstract

/-- The **WF-relativized** parallel reduction (`docs/DESIGN.md` §6's `Par'`): a `Par` step whose
*source* is well-formed. `abbrev` (not `def`) so the underlying `WF a ∧ Par a b` stays
transparent to `⟨·,·⟩`/`rcases`. -/
abbrev ParWF (a b : Term) : Prop := WF a ∧ Par a b

/-- The Takahashi triangle, **WF-scoped** (`WF e → Par e u → Par u (devel e)`); a thin alias of
`par_triangle` (now itself WF-scoped, since `alpha` makes the unconditional triangle false).
Stating the diamond against this name keeps `parWF_diamond` and the headline path stable as the
calculus grows. (There is deliberately no *unconditional* `par_diamond`/`par_confluent`/
`step_confluent` once `alpha` is present — those would be false; see `Confluence.lean`.) -/
theorem wf_par_triangle {e u : Term} (hwf : WF e) (h : Par e u) : Par u (devel e) :=
  par_triangle hwf h

/-- **The diamond for the WF-relativized reduction.** A fork `ParWF a b`, `ParWF a c` rejoins at
`d := devel a`: both legs by `wf_par_triangle` (the shared source `WF a`), and each target stays
`WF`-rooted by `WF.par`. Crucially this needs `WF` of the source `a` only — not of `devel a` — so
it discharges the *unconditional* premise `church_rosser` wants, for the relation `ParWF`. -/
theorem parWF_diamond : Diamond ParWF := by
  intro a b c hab hac
  obtain ⟨hwf, hab⟩ := hab
  obtain ⟨_, hac⟩ := hac
  exact ⟨devel a, ⟨WF.par hwf hab, wf_par_triangle hwf hab⟩,
                  ⟨WF.par hwf hac, wf_par_triangle hwf hac⟩⟩

/-- **Confluence of the WF-relativized reduction**, via the same generic
`Abstract.Diamond.confluent` (mathlib's `church_rosser`). `Confluence.lean` bridges this to the
`WF`-scoped headline `confluence` over `Step`. -/
theorem parWF_confluent : Confluent ParWF := parWF_diamond.confluent

end PhiConfluence
