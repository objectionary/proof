set_option autoImplicit false

variable (T : Type) -- fixed set of types

@[reducible]
def Ctx := List T

def Family := (Ctx T) → Type
def Familyₛ := T → (Ctx T) → Type

inductive I {T : Type} : Familyₛ T where
  | new
    : { α : T }
    → { ctx : Ctx T}
    → I α (α :: ctx)
  | old
    : { α β : T }
    → { ctx : Ctx T }
    → I α ctx
    → I α (β :: ctx)

def s_family_map
  {T : Type}
  (X : Familyₛ T)
  (Y : Familyₛ T)
  := {α : T} → {ctx : Ctx T} → X α ctx → Y α ctx

namespace Ctx
  -- context map
  def map {T : Type} (Γ : Ctx T) (X : Familyₛ T) (Δ : Ctx T) : Type
    := {α : T} → I α Γ → X α Δ

  def rename {T : Type} (Γ : Ctx T) (Δ : Ctx T) : Type
    := map Γ I Δ

end Ctx

def box {T : Type} (X : Familyₛ T) : Familyₛ T
  := λ α Γ => {Δ : Ctx T} → (Ctx.rename Γ Δ) → X α Δ

structure Coalg {T : Type} (X : Familyₛ T) where
  r : s_family_map X (box X)
  counit
    : {α : T}
    → {Γ : Ctx T}
    → { t : X α Γ}
    → r t id = t
  comult
    : {α : T}
    → {Γ Δ Θ : Ctx T}
    → {ρ₁ : Ctx.rename Γ Δ}
    → {ρ₂ : Ctx.rename Δ Θ}
    → {t : X α Γ}
    → r t (ρ₂ ∘ ρ₁) = r (r t ρ₁) ρ₂

structure PointedCoalg {T : Type} (X : Familyₛ T) where
  coalg : Coalg X
  η : s_family_map I X
  r_η
    : {α : T}
    → {Γ Δ : Ctx T}
    → {v : I α Γ}
    → {ρ : Ctx.rename Γ Δ}
    → coalg.r (η v) ρ = η (ρ v)

-- context extension
def deltaₛ {T : Type} (Θ : Ctx T) (X : Familyₛ T) : Familyₛ T
  := λ α Γ => X α (Θ ++ Γ)

----------------

-- "internal substitution hom" parametrizes 𝒴 by 𝒳-valued context map
def substHom {T : Type} : Familyₛ T → Familyₛ T → Familyₛ T
 := λ X Y α Γ => {Δ : Ctx T} → (Ctx.map Γ X Δ) → Y α Δ

structure Strength {T : Type} (F : Familyₛ T → Familyₛ T) where
  str
    (𝒫 : Familyₛ T )
    (ℬ : PointedCoalg 𝒫)
    (𝒳 : Familyₛ T)
    : s_family_map (F (substHom 𝒫 𝒳))  (substHom 𝒫 (F 𝒳))
  -- str-nat₁
  -- str-nat₂
  -- str-unit
  -- str-assoc

---------------

variable (O : Type) -- enumeration of operators

structure Signature where
  ops : O → List ((Ctx T) × T) × T
  arity : O → List ((Ctx T) × T) := λ o => (ops o).1
  sort  : O → T := λ o => (ops o).2

-- Simply typed lambda calculus
-- Set of types T is given as an inductive data type
inductive ΛT where
  | N : ΛT
  | Arrow : ΛT → ΛT → ΛT

-- enumeration of operators O
inductive Λₒ where
  | appₒ : {α β : ΛT} → Λₒ
  | lamₒ : {α β : ΛT} → Λₒ

def LamSig : Signature ΛT Λₒ :=
  { ops := fun o =>
      match o with
      | @Λₒ.appₒ α β => ([([], ΛT.Arrow α β), ([], α)], β)
      | @Λₒ.lamₒ α β => ([([α], β)], ΛT.Arrow α β)
  }

---------------

def Arg {T : Type} : List ((Ctx T) × T) → (Familyₛ T) → (Family T)
  | [], 𝒳, Γ => Unit
  | ((Θ , τ) :: as), 𝒳, Γ => deltaₛ Θ 𝒳 τ (Θ ++ Γ) × Arg as 𝒳 Γ

def SignatureEndofunctor {T O : Type} : (Signature T O) -> (Familyₛ T) → (Familyₛ T)
  -- PProd is Prod of Prop and Type
  := λ s 𝒳 α Γ => Σ (o : O), PProd (α = (s.sort o)) (Arg (s.arity o) 𝒳 Γ)

-------------

def str_sig
  {T O : Type}
  {s : Signature T O}
  : Strength (SignatureEndofunctor s)
  := sorry

def str_arg
  {T : Type}
  {𝒫 : Familyₛ T}
  (ℬ : PointedCoalg 𝒫)
  (𝒳 : Familyₛ T)
  (as : List ((Ctx T) × T))
  (Γ Δ : Ctx T)
  (σ : Ctx.map Γ 𝒫 Δ)
  : Arg as (substHom 𝒫 𝒳) Γ → Arg as 𝒳 Δ
  := match as with
  | [] => _
  | (Θ , τ) :: [] => fun h => h (lift ℬ Θ σ)
  | _ => _

--------------

inductive Tm {T O : Type} (s : Signature T O ) : Familyₛ T where
  | con
    : {τ : T}
    → {Γ : Ctx T}
    → (SignatureEndofunctor s) (Tm s) τ Γ → (Tm s) τ Γ
