import Minimal.Calculus
import Std.Tactic.Lint

def main : IO Unit :=
  IO.println "Lean 4!"

#lint only checkType checkUnivs defLemma dupNamespace explicitVarsOfIff impossibleInstance nonClassInstance simpComm simpNF simpVarHead synTaut unusedHavesSuffices in Minimal


-- #list_linters
-- rest of linters:
-- docBlame (*)
-- docBlameThm
-- unusedArguments (*)
