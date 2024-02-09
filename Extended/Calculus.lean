set_option autoImplicit false

@[reducible]
def Attr := String
@[reducible]
def Function := String
@[reducible]
def Bytes := String

-- inductive Attr where
--   | φ : Attr
--   | ρ : Attr
--   | σ : Attr
--   | ν : Attr
--   | α : String → Attr

mutual
  inductive Binder : Attr → Type where
    | alpha : (a : Attr) → Term → Binder a
    | empty : (a : Attr) → Binder a
    | delta : Bytes → Binder "Δ"
    | lambda : Function → Binder "λ"

  inductive Bindings : List Attr → Type where
    | nil : Bindings []
    | cons
      : { lst : List Attr }
      → { a : Attr }
      → a ∉ lst
      → Binder a
      → Bindings lst
      → Bindings (a :: lst)

  inductive Term : Type where
    | obj : { attrs : List Attr } → Bindings attrs → Term -- ⟦ α₁ ↦ u₁, ... αₖ ↦ uₖ ⟧
    | app : { attrs : List Attr } → Term → Bindings attrs → Term  -- t(α₁ ↦ u₁, ... αₖ ↦ uₖ)
    -- | obj : Bindings _ → Term
    -- | app : Term → Bindings _ → Term
    | dot : Term → Attr → Term      -- t.a
    | glob : Term                   -- Φ
    | this : Term                   -- ξ
    | termination : Term            -- ⊥
end
open Term

namespace Bindings

  def singleton (a : Attr) (t : Term) : Bindings [a]
    := cons (λ isin => by contradiction) (Binder.alpha a t) nil

end Bindings

inductive IsAttached : { attrs : List Attr } → Attr → Term → Bindings attrs → Type where
  -- | zeroth_attached
  --   : { lst : List Attr }
  --   → (a : Attr)
  --   → (not_in : a ∉ lst)
  --   → (t : Term)
  --   → (l : Bindings lst)
  --   → IsAttached a t (Bindings.cons a not_in (attached t) l)
  -- | next_attached
  --   : { lst : List Attr }
  --   → (a : Attr)
  --   → (t : Term)
  --   → (l : Bindings lst)
  --   → (b : Attr)
  --   → (a ≠ b)
  --   → (not_in : b ∉ lst)
  --   → (u : OptionalAttr)
  --   → IsAttached a t l
  --   → IsAttached a t (Bindings.cons b not_in u l)

inductive IsVoid : { attrs : List Attr } → Attr → Bindings attrs → Type

universe u v
inductive ForAll : { α : Type u } → (f : α → Type v) → (List α) → Prop where
  | nil : { α : Type u } → { f : α → Type v } → ForAll f []
  | cons : { α : Type u } → { f : α → Type v } → (l : List α) → (a : α) → (fa : f a) → ForAll f l → ForAll f (a :: l)

def insert
  { attrs : List Attr }
  (bnds : Bindings attrs)
  (a : Attr)
  (u : Term)
  : (Bindings attrs)
  := sorry

def remove
  { attrs : List Attr }
  (bnds : Bindings attrs)
  (a : Attr)
  : Bindings (List.removeAll attrs [a])
  := sorry

def insertAll
  { attrs_from : List Attr }
  { attrs_to : List Attr }
  (bnds_from : Bindings attrs_from)
  (bnds_to : Bindings attrs_to)
  : (Bindings attrs_to)
  := sorry

def subst_this_head
  (t : Term)
  (u : Term)
  : Term
  := match t with
    | obj bnds => obj bnds
    | app t' bnds => app t' bnds
    | dot t' a => dot (subst_this_head t' u) a
    | glob => glob
    | this => u
    | termination => termination

inductive NormalForm : Term → Type where
  | nf : (t : Term) → NormalForm t

inductive Prog : Type where
  | prog : { attrs : List Attr } → Bindings attrs → Prog
def get_bindings (prog : Prog) : Σ attrs : List Attr, Bindings attrs
  := match prog with
    | @Prog.prog attrs bnds => ⟨attrs, bnds⟩

inductive Reduce : Prog → Term → Term → Type where
  | congDot
    : { a : Attr }
    → { t t' : Term }
    → { prog : Prog }
    → Reduce prog t t'
    → Reduce prog (dot t a) (dot t' a)
  | congObj
    : { a : Attr }
    → { t t' : Term }
    → { prog : Prog }
    → { attrs : List Attr }
    → { bnds : Bindings attrs }
    → IsAttached a t bnds
    → Reduce prog t t' -- Φ ↦ ⟦B⟧ ⊢ t ⇝ t'
    → Reduce
      prog
      (obj bnds) -- ⟦ a ↦ t, B ⟧
      (obj (insert bnds a t')) -- ⟦ a ↦ t', B ⟧
  | r4
    : { prog : Prog }
    → Reduce
      prog -- Φ ↦ ⟦B⟧
      glob -- Φ
      (obj (insert (get_bindings prog).snd "σ" glob)) -- ⟦ B, σ ↦ Φ ⟧
  | r5
    : { prog : Prog }
    → { a : Attr }
    → { attrs : List Attr }
    → { bnds : Bindings attrs }
    → (t : Term)
    → IsAttached a t bnds
    → Reduce
      prog
      (obj bnds) -- ⟦ a ↦ ξ • t', B ⟧
      (obj (insert bnds a (subst_this_head t (obj bnds)))) -- ⟦ a ↦ ⟦B⟧ • t', B ⟧   ?add recursion?
  | r6
    : { a : Attr }
    → { attrs : List Attr }
    → { bnds : Bindings attrs } -- B
    → (n : Term)
    → IsAttached a n bnds
    → (prog : Prog)
    → NormalForm n
    → Reduce
      prog
      (dot (obj bnds) a) -- ⟦ a ↦ n, B ⟧.a
      (app n (Bindings.singleton "ρ" (obj (remove bnds a)))) -- n(ρ ↦ ⟦B⟧), ?should keep a ↦ n?
  | r7
    : { attrs : List Attr }
    → { bnds : Bindings attrs }
    → { void_attrs : List Attr }
    → ForAll (λ a => IsVoid a bnds) void_attrs
    → (prog : Prog)
    → (void_bnds : Bindings void_attrs)
    → Reduce
      prog
      (app (obj bnds) void_bnds) -- ⟦ τ₁ ↦ ∅, τ₂ ↦ ∅, ... B⟧(τ₁ ↦ n₁, τ₂ ↦ n₂, ...)
      (obj (insertAll void_bnds (remove bnds "ν"))) -- ⟦ τ₁ ↦ n₁, τ₂ ↦ n₂, ... B ─ ν ⟧
  | r8
    : { a : Attr }
    → { attrs : List Attr }
    → { bnds : Bindings attrs }
    → (prog : Prog)
    → a ∉ attrs
    → (n : Term)
    → NormalForm n
    → IsAttached "φ" n bnds
    → Reduce
      prog
      (dot (obj bnds) a) -- ⟦ φ ↦ n, B ⟧.a
      (dot n a) -- n.a
  | r9
    : { attrs : List Attr }
    → { bnds : Bindings attrs }
    → { n : Term }
    → (prog : Prog)
    → NormalForm n
    → Reduce
      prog
      (app (obj bnds) (Bindings.singleton "ρ" n)) -- ⟦ B ⟧(ρ ↦ n)
      (obj (insert bnds "ρ" n)) -- ⟦ ρ ↦ n, B ─ ρ ⟧

inductive Context where
  | prog : { attrs : List Attr } → Bindings attrs → Context
  | cons : { attrs : List Attr } → Bindings attrs → Context → Context

def top (ctx : Context) : Σ attrs : List Attr, Bindings attrs
  := match ctx with
    | @Context.prog a b => ⟨a, b⟩
    | @Context.cons a b _ => ⟨a, b⟩

def getProg (ctx : Context) : Σ attrs : List Attr, Bindings attrs
  := match ctx with
    | @Context.prog a b => ⟨a, b⟩
    | Context.cons _ c => getProg c

mutual
  inductive Entails : Context → Term → Type where
    -- | ???

-- infix:20 " ⊢ " => WithContext.entails
  inductive ReduceCtx : Context → Term → Term → Type where
    | congDot
      : { a : Attr }
      → { t t' : Term }
      → { ctx : Context }
      → ReduceCtx ctx t t'
      → ReduceCtx ctx (dot t a) (dot t' a)
    | congObj
      : { a : Attr }
      → { t t' : Term }
      → { ctx : Context }
      → { attrs : List Attr }
      → { bnds : Bindings attrs }
      → IsAttached a t bnds
      → ReduceCtx (Context.cons (remove bnds a) ctx) t t' -- ⟦B⟧ ⊢ t ⇝ t'
      → ReduceCtx
        ctx
        (obj bnds) -- ⟦ a ↦ t, B ⟧
        (obj (insert bnds a t')) -- ⟦ a ↦ t', B ⟧
    | r4
      : { ctx : Context }
      → ReduceCtx
        ctx -- ⟦B⟧, Γ
        glob -- Φ
        (obj (insert (getProg ctx).snd "σ" glob)) -- ⟦ B, σ ↦ Φ ⟧
    | r5
      : { ctx : Context }
      → { attrs : List Attr }
      → { bnds : Bindings attrs }
      → ReduceCtx
        (Context.cons bnds ctx) -- Γ , ⟦ B ⟧    ?ᵃ?
        this -- ξ
        (obj bnds) -- ⟦ B ⟧
    | r6
      : { a : Attr }
      → { attrs : List Attr }
      → { bnds : Bindings attrs } -- B
      → a ∉ attrs
      → (n : Term)
      → (ctx : Context) -- Γ
      → Entails (Context.cons bnds ctx) n -- Γ, ⟦B⟧ ⊢ n
      → NormalForm n
      → ReduceCtx
        ctx
        (dot (obj (insert bnds a n)) a) -- ⟦ a ↦ n, B ⟧.a
        (app n (Bindings.singleton "ρ" (obj bnds))) -- n(ρ ↦ ⟦ B ⟧), ?should add a ↦ n?
    | r7
      : { attrs : List Attr }
      → { bnds : Bindings attrs }
      → { void_attrs : List Attr }
      → ForAll (λ a => IsVoid a bnds) void_attrs
      → (ctx : Context)
      → (void_bnds : Bindings void_attrs)
      → ReduceCtx
        ctx
        (app (obj bnds) void_bnds) -- ⟦ τ₁ ↦ ∅, τ₂ ↦ ∅, ... B⟧(τ₁ ↦ n₁, τ₂ ↦ n₂, ...)
        (obj (insertAll void_bnds bnds)) -- ⟦ τ₁ ↦ n₁, τ₂ ↦ n₂, ... B ⟧ todo: B ─ ν
    | r8
      : { a : Attr }
      → { attrs : List Attr }
      → { bnds : Bindings attrs }
      → (ctx : Context)
      → a ∉ attrs
      → (n : Term)
      → NormalForm n
      → IsAttached "φ" n bnds
      → ReduceCtx
        ctx
        (dot (obj bnds) a)
        (dot n a)
    | r9
      : { attrs : List Attr }
      → { bnds : Bindings attrs }
      → { n : Term }
      → (ctx : Context)
      → NormalForm n
      → ReduceCtx
        ctx
        (app (obj bnds) (Bindings.singleton "ρ" n)) -- ⟦ B ⟧(ρ ↦ n)
        (obj (insert bnds "ρ" n)) -- ⟦ ρ ↦ n, B ─ ρ ⟧
end
