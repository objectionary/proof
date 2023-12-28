import Minimal.calculus

set_option autoImplicit false

open OptionalAttr
open Term


mutual
partial def termToString : Term → String
  | Term.loc n => s!"ρ{n}"
  | Term.dot t s => s!"{termToString t}.{s}"
  | Term.app t a u => s!"{termToString t}({a} ↦ {termToString u})"
  | Term.obj o =>
    "〚" ++ listToString o ++ "〛"

partial def listToString : List (Attr × OptionalAttr) → String
      | [] => ""
      | [(a, t)] => s!"{a} ↦ {attrToString t}"
      | List.cons (a, t) l => s!"{a} ↦ {attrToString t}, " ++ (listToString l)

partial def attrToString : OptionalAttr → String
  | attached x => termToString x
  | void => "∅"
end


instance : ToString OptionalAttr where
  toString := attrToString

instance : ToString Term where
  toString := termToString


#eval whnf (app (dot (obj [("x", attached (obj [("y", void)]))]) "x") "y" (dot (obj [("z", attached (loc 3)), ("w", void)]) "z"))

#eval nf (app (dot (obj [("x", attached (obj [("y", void)]))]) "x") "y" (dot (obj [("z", attached (loc 3)), ("w", void)]) "z"))
