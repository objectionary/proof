import SOAS.Term

set_option autoImplicit false

inductive ΛT where
  | Base : ΛT
  | Arrow : ΛT → ΛT → ΛT
open ΛT

inductive Λₒ where
  | appₒ : {α β : ΛT} → Λₒ
  | lamₒ : {α β : ΛT} → Λₒ
open Λₒ

def LamSig : Signature ΛT Λₒ :=
  { ops := fun o =>
      match o with
      | @Λₒ.appₒ α β => ([([], ΛT.Arrow α β), ([], α)], β)
      | @Λₒ.lamₒ α β => ([([α], β)], ΛT.Arrow α β)
  }

-- λ x:B. x
def identity {Γ : Ctx ΛT}
  : Term ΛT Λₒ LamSig Base (Base :: Γ)
  := Term.var I.new

-- B → B
@[reducible]
def bb : ΛT := Arrow Base Base

-- λ f: B → B. λ x: B. f (f x)
def twice {Γ : Ctx ΛT}
  : Term ΛT Λₒ LamSig (Arrow bb bb) (Γ)
  := Term.con (@lamₒ bb bb) rfl
      (Arg.cons (Term.con (@lamₒ Base Base) rfl (Arg.cons
        (Term.con (@appₒ Base Base) rfl (Arg.cons (Term.var (I.old I.new)) (Arg.cons
          (Term.con (@appₒ Base Base) rfl (Arg.cons (Term.var (I.old I.new)) (Arg.cons (Term.var I.new) Arg.nil)) _ Γ)
        Arg.nil)) _ Γ)
      Arg.nil) _ Γ) Arg.nil)
    _ Γ
