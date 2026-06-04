-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

/-!
# Schema for the generated rule data

The typed vocabulary that `PhiConfluence/RuleData.lean` (generated from phino by
`scripts/gen-rule-data.py`) is written in: each normalization rule is a `RuleEntry` of
tags — the redex it fires on, its side-conditions, and its contractum. These are *data*
describing the eleven `phino` rules; the proof relation `Step` (`Step.lean`) is the
authoritative hand-written object, and `RuleData.lean` is kept identical to phino by the
`rule-data-in-sync` CI job.
-/

namespace PhiConfluence

/-- Which redex a rule fires on: `⊥.a`, `⊥(a↦arg)`, `⟦bs⟧.a`, or `⟦bs⟧(a↦arg)`. -/
inductive RedexShape where
  | dispatchBot | appBot | dispatchForm | appForm
  deriving Repr, DecidableEq

/-- A side condition on the redex's formation, attribute, and argument. -/
inductive Cond where
  | slotVoid | slotAttached | slotAbsent
  | attrNeRho | attrIsRho | attrNotAlpha
  | phiAbsent | phiPresent | noLambda
  | valNf | argXiFree | argNf | alphaVoidOrdinal
  deriving Repr, DecidableEq

/-- The contractum a rule rewrites its redex to. -/
inductive Contractum where
  | bot | formSame | phiExpand | dotFeedback | copyFill | alphaRename
  deriving Repr, DecidableEq

/-- One normalization rule as structured data. (Named `RuleEntry`, not `RuleSpec`,
to avoid colliding with `Render.lean`'s display-string `RuleSpec`.) -/
structure RuleEntry where
  name  : String
  shape : RedexShape
  conds : List Cond
  rhs   : Contractum

end PhiConfluence
