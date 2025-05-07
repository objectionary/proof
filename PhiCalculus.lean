-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Minimal.ARS
import Minimal.Reduction.Regular.Confluence
import Batteries.Tactic.Lint

-- these are all Std linters except docBlame and docBlameThm
#lint only checkType checkUnivs defLemma dupNamespace explicitVarsOfIff impossibleInstance nonClassInstance simpComm simpNF simpVarHead synTaut unusedArguments unusedHavesSuffices in Minimal
