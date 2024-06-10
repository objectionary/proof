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
  : Term LamSig Base (Base :: Γ)
  := Term.var I.new

-- B → B
@[reducible]
def bb : ΛT := Arrow Base Base

-- λ f: B → B. λ x: B. f (f x)
def twice {Γ : Ctx ΛT}
  : Term LamSig (Arrow bb bb) Γ
  := Term.con (@lamₒ bb bb) rfl
      (Arg.cons (Term.con (@lamₒ Base Base) rfl (Arg.cons
        (Term.con (@appₒ Base Base) rfl (Arg.cons (Term.var (I.old I.new)) (Arg.cons
          (Term.con (@appₒ Base Base) rfl (Arg.cons (Term.var (I.old I.new)) (Arg.cons (Term.var I.new) Arg.nil)))
        Arg.nil)))
      Arg.nil)) Arg.nil)

-- (λ x. M[x]) N[] ⇝ M[N[]]
def beta {α β : ΛT} {Γ : Ctx ΛT} : @RewriteRule ΛT Λₒ LamSig β Γ
  := RewriteRule.mk
      (Term.con (@appₒ α β) rfl
        (Arg.cons
          (Term.con (@lamₒ α β) rfl (Arg.cons
            (Term.mvar M (App.cons (Term.var I.new) App.nil)) Arg.nil)
          )
          (Arg.cons (Term.mvar N App.nil) Arg.nil)
        )
      )
      (Term.mvar
        -- (Metavar.mk "M")
        M
        (App.cons (Term.mvar N (App.nil)) App.nil)
      )
  where
    M := @Metavar.mk ΛT β [α] "M"
    N := @Metavar.mk ΛT α [] "N"

-- (λ x. M[] x) ⇝ M[]
def eta {α β : ΛT} {Γ : Ctx ΛT} : @RewriteRule ΛT Λₒ LamSig (Arrow α β) Γ
  := RewriteRule.mk
      (Term.con (@lamₒ α β) rfl
        (Arg.cons
          (Term.con (@appₒ α β) rfl
            (Arg.cons
              (Term.mvar M App.nil)
              (Arg.cons (Term.var I.new) Arg.nil)
            )
          )
          Arg.nil
        )
      )
      (Term.mvar M App.nil)
  where
    M := @Metavar.mk ΛT (Arrow α β) [] "M"
