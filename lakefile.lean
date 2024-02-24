import Lake
open Lake DSL

package «phi-calculus»

require std from git "https://github.com/leanprover/std4" @ "main"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib PhiCalculus

lean_lib Minimal
