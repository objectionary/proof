set_option autoImplicit false

-- example with free monad:
-- https://stackoverflow.com/questions/78274957/how-to-define-free-monads-and-cofree-comonads-in-lean4
-- data Free (f :: Type -> Type) (a :: Type)
--   = Pure a
--   | Free (f (Free f a))

inductive Free (f : Type → Type) (α : Type) where
  | pure : α → Free f α
  | free : ∀ x, f x -> (x -> Free f α) → Free f α

--------

namespace FS
-- Free Scoped

inductive Inc (var : Type) : Type where
  | Z : Inc var
  | S : var → Inc var

def Scope (term : Type → Type) (var : Type) := term (Inc var)

-- data FS t a
--   = Pure a
--   | Free (t (Scope (FS t) a) (FS t a))

inductive FS' (t : Type → Type → Type) (a : Type) where
  | Pure : a → FS' t a
  -- | Free
  --   : ∀ x y, t x y
  --   -- -> (x → (Scope (FS' t) a))
  --   -> (x → (FS' t (Inc a)))
  --   -> (y → (FS' t a))
  --   -> FS' t a

inductive FS : (t : Type → Type → Type 1) → (a : Type) → Type 1 where
  | Pure (t : Type → Type → Type 1) (a : Type) : a → FS t a
  | Free
    (t : Type → Type → Type 1)
    (a : Type)
    : ∀ x y, t x y
    -- -> (x → (Scope (FS t) a))
    -> (x → (FS t (Inc a)))
    -> (y → (FS t a))
    -> FS t a

-- data TermF scope term
--   = AppF term term
--   | LamF scope

inductive TermF (scope : Type) (term : Type) : Type 1 where
  | AppF : term → term → TermF scope term
  | LamF : scope → TermF scope term

-- type Term a = FS TermF a
def Term a := FS TermF a

-- substitute :: Monad term => term a -> Scope term a -> term a
-- substitute u s = s >>= \x -> case x of
--   Z -> u -- substitute bound variable
--   S y -> return y -- keep free variable

-- whnf :: Term a -> Term a
-- whnf term = case term of
--   App fun arg -> case whnf fun of
--   Lam body -> whnf (substitute arg body) fun' -> App fun' arg
--   _ -> term

partial def whnf {a : Type} : Term a → Term a
  := fun term => match term with
  | FS.Pure _ _ _ => term
  | FS.Free _ _ _ _ (TermF.LamF _) _ _ => term
  | FS.Free _ _ _ _ (TermF.AppF func arg) _ _ =>
    match (whnf func) with
    -- | FS.Free _ _ _ _ (TermF.LamF _) _ _ => term
    | _ => sorry


end FS
--------

def Ctx (T : Type) := List T
def Family {T : Type}  := Ctx T → Type

-- inductive Term (Sig : Family → Family) (M : Type) : Family where
--   | var : (X : Ctx) → Nat → Term Sig M X
--   | op  : (X : Ctx) → Sig (Term Sig M) X → Term Sig M X
--   | metavar : (X : Ctx) → M → List (Term Sig M X) → Term Sig M X
inductive Term {T : Type} (Sig : Family → Family) (M : Type) (X : Ctx T) : Type _ where
  | var : Nat → Term Sig M X
  | op  : ∀ x, Sig x X → (x X → (Term Sig M) X)→ Term Sig M X
  | metavar : M → List (Term Sig M X) → Term Sig M X

inductive ΛT where
  | N : ΛT
  | Arrow : ΛT → ΛT → ΛT

-- inductive LamSig (Tm : Family) : Family where
--   | app : (X : Ctx) → Tm X → Tm X → LamSig Tm X
--   | lam : (X : Ctx) → Tm (_ :: X) → LamSig Tm X
inductive LamSig (Tm : Family) : Family where
  | app : (X : Ctx ΛT) → Tm X → Tm X → LamSig Tm X
  | lam : (X : Ctx ΛT) → Tm (_ :: X) → LamSig Tm X
