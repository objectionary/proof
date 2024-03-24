import Minimal.ARS
import Minimal.Calculus
import Std.Tactic.Lint

-- these are all Std linters except docBlame and docBlameThm
#lint only checkType checkUnivs defLemma dupNamespace explicitVarsOfIff impossibleInstance nonClassInstance simpComm simpNF simpVarHead synTaut unusedArguments unusedHavesSuffices in Minimal
