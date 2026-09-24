-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

/-!
# Schema for the generated rule data

The typed vocabulary that `PhiConfluence/RuleData.lean` (generated from phino by
`.github/gen-rule-data.py`) is written in: each normalization rule is a `RuleEntry` of
tags — the redex it fires on, its side-conditions, and its contractum. These are *data*
describing the fifteen `phino` rules; the proof relation `Step` (`Step.lean`) is the
authoritative hand-written object. `RuleData.lean` is not tracked by Git:
`.github/regen-rules.sh` generates it from the pinned phino before every build.
-/

namespace PhiConfluence

/-- Which redex a rule fires on: `⊥.a`, `⊥(a↦arg)`, `⟦bs⟧.a`, `⟦bs⟧(a↦arg)`, or `⟦bs⟧` itself. -/
inductive RedexShape where
  | dispatchBot | appBot | dispatchForm | appForm | form
  deriving Repr, DecidableEq

/-- A side condition on the redex's formation, attribute, and argument. -/
inductive Cond where
  | slotVoid | slotAttached | slotAbsent
  | attrNeRho | attrIsRho | attrNotAlpha | attrIsAlpha
  | phiAbsent | noLambda | lambdaPresent | deltaPresent | notLambdaWithDelta
  | valNf | argXiFree | argNf
  | ordinalVoid | ordinalAttached | ordinalAbsent
  | notUniverse | isUniverse
  deriving Repr, DecidableEq

/-- The contractum a rule rewrites its redex to. -/
inductive Contractum where
  | bot | formSame | dotFeedback | dotGlobal | copyFill | alphaRename
  deriving Repr, DecidableEq

/-- One normalization rule as structured data. (Named `RuleEntry`, not `RuleSpec`,
to avoid colliding with `Render.lean`'s display-string `RuleSpec`.) -/
structure RuleEntry where
  name  : String
  shape : RedexShape
  conds : List Cond
  rhs   : Contractum

end PhiConfluence
