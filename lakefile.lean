-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Lake
open Lake DSL

package «phi-calculus»

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require batteries from
  git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib PhiCalculus

lean_lib Minimal
lean_lib Extended
