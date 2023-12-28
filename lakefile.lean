import Lake
open Lake DSL

package «phi-calculus»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require std from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib PhiCalculus

lean_lib Minimal
