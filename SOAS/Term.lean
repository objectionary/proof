set_option autoImplicit false

variable (T : Type) -- fixed set of types
variable (O : Type) -- enumeration of operators

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

structure Signature where
  ops : O → List ((Ctx T) × T) × T
  arity : O → List ((Ctx T) × T) := λ o => (ops o).1
  sort  : O → T := λ o => (ops o).2

mutual
  inductive Term (s : Signature T O) : (α : T) → (Ctx T) → Type 1 where
    | var : {α : T} → {Γ : Ctx T} → I α Γ → Term s α Γ
    | con
      : {α : T}
      → {Γ : Ctx T}
      → (o : O)
      → (α = s.sort o)
      → Arg s (s.arity o) Γ
      → Term s α Γ
    -- | mvar

  inductive Arg (s : Signature T O) : List ((Ctx T) × T) → Ctx T → Type 1 where
    | nil  : {Γ : Ctx T} → Arg s [] Γ
    | cons
      : {τ : T}
      → {Γ : Ctx T}
      → {Θ : Ctx T}
      → {l : List ((Ctx T) × T)}
      → Term s τ (Θ ++ Γ)
      → Arg s l Γ
      → Arg s ((Θ, τ) :: l) Γ
end
