import Lake
open Lake DSL

package «phi-calculus» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib PhiCalculus {
  -- add any library configuration options here
}
