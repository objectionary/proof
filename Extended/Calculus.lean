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
  -- inductive Binder : Attr → Type where
  --   | alpha : (a : Attr) → Term → Binder a
  --   | empty : (a : Attr) → Binder a
    -- | delta : Bytes → Binder "Δ"
    -- | lambda : Function → Binder "λ"

  inductive Bindings : List Attr → Type where
    | nil : Bindings []
    | cons
      : { lst : List Attr }
      → { a : Attr }
      → a ∉ lst
      -- → Binder a
      → Option Term
      → Bindings lst
      → Bindings (a :: lst)

  inductive Term : Type where
    | obj : { attrs : List Attr } → Bindings attrs → Term -- ⟦ α₁ ↦ u₁, ... αₖ ↦ uₖ ⟧
    | app : { attrs : List Attr } → Term → Bindings attrs → Term  -- t(α₁ ↦ u₁, ... αₖ ↦ uₖ)
    | dot : Term → Attr → Term      -- t.a
    | glob : Term                   -- Φ
    | this : Term                   -- ξ
    -- | termination : Term            -- ⊥
end
open Term



namespace Bindings

  def singleton (a : Attr) (t : Term) : Bindings [a]
    -- := cons (λ isin => by contradiction) (Binder.alpha a t) nil
    := cons (λ isin => by contradiction) (some t) nil

  -- inductive ForEach : { attrs : List Attr } → (Term → Prop) → (Bindings attrs) → Type where
    -- | nil : { f : Term → Prop } → ForEach f Bindings.nil
    -- | consVoid : {}

end Bindings

--\ A value is an object formation where all attributes have values attached to them
mutual
  inductive IsValue : Term → Type where
    | is_value
      : { attrs : List Attr }
      → (bnds : Bindings attrs)
      → AllValue bnds
      → IsValue (obj bnds)

  inductive AllValue : { attrs : List Attr } → Bindings attrs → Type where
    | nil : AllValue Bindings.nil
    | cons
      : { attrs : List Attr }
      → (bnds : Bindings attrs)
      → (t : Term)
      → { a : Attr }
      → (not_in : a ∉ attrs)
      → IsValue t
      → AllValue (Bindings.cons not_in (some t) bnds)
end

inductive IsAttached : { attrs : List Attr } → Attr → Term → Bindings attrs → Type where

namespace IsAttached
  def attached_eq
    { a : Attr }
    { t t' : Term }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    (is_attached : IsAttached a t bnds)
    (is_attached' : IsAttached a t' bnds)
    : t = t'
    := sorry

  def attached_is_in
    { a : Attr }
    { t : Term }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    (is_attached : IsAttached a t bnds)
    : a ∈ attrs
    := sorry

end IsAttached

inductive IsVoid : { attrs : List Attr } → Attr → Bindings attrs → Type
  | this
    : { a : Attr }
    → { attrs : List Attr }
    → { bnds : Bindings attrs }
    → { not_in : a ∉ attrs }
    → IsVoid a (Bindings.cons not_in none bnds)
  | next
    : { a b : Attr }
    → { attrs : List Attr }
    → { bnds : Bindings attrs }
    → { not_in : b ∉ attrs }
    → { ot : Option Term }
    → IsVoid a bnds
    → IsVoid a (Bindings.cons not_in ot bnds)

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

namespace Insert
  def insert_attached
    { a : Attr }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { t : Term }
    (is_attached : IsAttached a t bnds)
    : insert bnds a t = bnds
    := sorry

  def attached_after_insert
    { a : Attr }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { t : Term }
    (is_in : a ∈ attrs)
    : IsAttached a t (insert bnds a t)
    := sorry

  def insert_second
    { a : Attr }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { t t' : Term }
    : insert (insert bnds a t) a t' = insert bnds a t'
    := sorry

  def insert_new_attached
    { a : Attr }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { t : Term}
    : IsAttached a t (insert bnds a t)
    := sorry

  def insert_swap
    { a1 a2 : Attr }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { t1 t2 : Term }
    (neq : a1 ≠ a2)
    : insert (insert bnds a1 t1) a2 t2 = insert (insert bnds a2 t2) a1 t1
    := sorry

  def insert_another_keeps_attached
    { a1 a2 : Attr }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { t1 t2 : Term }
    (neq : a1 ≠ a2)
    (is_attached : IsAttached a1 t1 bnds)
    : IsAttached a1 t1 (insert bnds a2 t2)
    := sorry

  def insert_remove
    { a : Attr }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { t : Term }
    : remove (insert bnds a t) a = remove bnds a
    := sorry

end Insert

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
      → IsAttached a t bnds -- ⟦ a ↦ t, B ⟧
      → ReduceCtx (Context.cons (remove bnds a) ctx) t t' -- ⟦B⟧ ⊢ t ⇝ t'
      → ReduceCtx
        ctx
        (obj bnds) -- ⟦ a ↦ t, B ⟧
        (obj (insert bnds a t')) -- ⟦ a ↦ t', B ⟧
    | congAppL
      : { t t' : Term }
      → { ctx : Context }
      → { attrs : List Attr }
      → { bnds : Bindings attrs }
      → ReduceCtx ctx t t'
      → ReduceCtx
        ctx
        (app t bnds)
        (app t' bnds)
    | congAppR
      : { a : Attr }
      → { t u u' : Term }
      → { ctx : Context }
      → { attrs : List Attr }
      → { bnds : Bindings attrs }
      → IsAttached a u bnds
      → ReduceCtx ctx u u' -- Φ ⊢ u ⇝ u'
      → ReduceCtx
        ctx
        (app t bnds) -- t(τ₁ ↦ t₁, ... a ↦ u, ...)
        (app t (insert bnds a u')) -- t(τ₁ ↦ t₁, ... a ↦ u', ...)
    | r4
      : { ctx : Context }
      → ReduceCtx
        ctx -- ⟦B⟧, Γ
        glob -- Φ
        (obj (insert (getProg ctx).snd "σ" glob)) -- ⟦ B, σ ↦ Φ ⟧
    -- | r5
    --   : { ctx : Context }
    --   → { attrs : List Attr }
    --   → { bnds : Bindings attrs }
    --   → ReduceCtx
    --     (Context.cons bnds ctx) -- Γ , ⟦ B ⟧    ?ᵃ?
    --     this -- ξ
    --     (obj bnds) -- ⟦ B ⟧
    | r5
      : { ctx : Context }
      → ReduceCtx
        ctx -- Γ , ⟦ B ⟧    ?ᵃ?
        this -- ξ
        (obj (top ctx).snd) -- ⟦ B ⟧
    | r6
      : { a : Attr }
      → { attrs : List Attr }
      → { bnds : Bindings attrs } -- B, a ↦ n
      → { ctx : Context } -- Γ
      → (n : Term)
      → IsAttached a n bnds
      → IsValue n
      → ReduceCtx
        ctx
        (dot (obj bnds) a) -- ⟦ a ↦ n, B ⟧.a
        (app n (Bindings.singleton "ρ" (obj (remove bnds a)))) -- n(ρ ↦ ⟦ B ⟧), ?should add a ↦ n?
    | r7
      : { attrs : List Attr }
      → { bnds : Bindings attrs }
      → { void_attrs : List Attr }
      → { ctx : Context }
      → ForAll (λ a => IsVoid a bnds) void_attrs
      → (void_bnds : Bindings void_attrs)
      → AllValue void_bnds
      → ReduceCtx
        ctx
        (app (obj bnds) void_bnds) -- ⟦ τ₁ ↦ ∅, τ₂ ↦ ∅, ... B⟧(τ₁ ↦ n₁, τ₂ ↦ n₂, ...)
        (obj (remove (insertAll void_bnds bnds) "ν")) -- ⟦ τ₁ ↦ n₁, τ₂ ↦ n₂, ... B ─ ν ⟧
    | r8
      : { a : Attr }
      → { attrs : List Attr }
      → { bnds : Bindings attrs }
      → { ctx : Context }
      → a ∉ attrs
      → (n : Term)
      → IsValue n
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
      → IsValue n
      → IsValue (obj bnds)
      → ReduceCtx
        ctx
        (app (obj bnds) (Bindings.singleton "ρ" n)) -- ⟦ B ⟧(ρ ↦ n)
        (obj (insert bnds "ρ" n)) -- ⟦ ρ ↦ n, B ─ ρ ⟧
end
open ReduceCtx

inductive RedMany : Context → Term → Term → Type where
  | nil : { m : Term } → { ctx : Context } → RedMany ctx m m
  | cons
    : { l m n : Term}
    → { ctx : Context }
    → ReduceCtx ctx l m
    → RedMany ctx m n
    → RedMany ctx l n

def cong_dot_clos
  { t t' : Term }
  { a : Attr }
  { ctx : Context }
  (reds : RedMany ctx t t')
  : (RedMany ctx (dot t a) (dot t' a))
  := match reds with
    | RedMany.nil => RedMany.nil
    | RedMany.cons red reds' =>
      RedMany.cons (congDot red) (cong_dot_clos reds')

def cong_obj_clos
  { t t' : Term }
  { a : Attr }
  { attrs : List Attr }
  { bnds : Bindings attrs }
  { ctx : Context }
  (reds : RedMany (Context.cons (remove bnds a) ctx) t t')
  (is_attached : IsAttached a t bnds)
  : (RedMany ctx (obj bnds) (obj (insert bnds a t')))
  := match reds with
    | RedMany.nil => by
      simp [Insert.insert_attached is_attached]
      exact RedMany.nil
    | @RedMany.cons _ t_i _ _ red reds' =>
      let bnds' := insert bnds a t_i
      let reductions
        : RedMany (Context.cons (remove bnds' a) ctx) t_i t'
        := reds'
      let ind_hypothesis
        : RedMany ctx (obj bnds') (obj (insert bnds' a t'))
        := cong_obj_clos reductions (Insert.attached_after_insert (is_attached.attached_is_in))
      RedMany.cons (congObj is_attached red) ind_hypothesis

def cong_obj_insert_clos
  { t t' : Term }
  { a : Attr }
  { attrs : List Attr }
  { bnds : Bindings attrs }
  { ctx : Context }
  (reds : RedMany (Context.cons (remove bnds a) ctx) t t')
  : (RedMany ctx (obj (insert bnds a t)) (obj (insert bnds a t')))
  := match reds with
    | RedMany.nil => RedMany.nil
    | @RedMany.cons _ t_i _ _ red reds' =>
      let is_attached_ti : IsAttached a t (insert bnds a t) := Insert.insert_new_attached
      RedMany.cons (congObj is_attached_ti red) (cong_obj_insert_clos reds')

def cong_appₗ_clos
  { t t' : Term }
  { attrs : List Attr }
  { bnds : Bindings attrs }
  { ctx : Context }
  (reds : RedMany ctx t t')
  : (RedMany ctx (app t bnds) (app t' bnds))
  := match reds with
    | RedMany.nil => RedMany.nil
    | RedMany.cons red reds' => RedMany.cons (congAppL red) (cong_appₗ_clos reds')

def cong_appᵣ_clos
  { a : Attr }
  { t u u' : Term }
  { attrs : List Attr }
  { bnds : Bindings attrs }
  { ctx : Context }
  (reds : RedMany ctx u u')
  (is_attached : IsAttached a u bnds)
  : (RedMany ctx (app t bnds) (app t (insert bnds a u')))
  := match reds with
    | RedMany.nil => by
      rw [Insert.insert_attached is_attached]
      exact RedMany.nil
    | @RedMany.cons _ u_i _ _ red reds' =>
      let ind_hypothesis
        : RedMany ctx (app t (insert bnds a u_i)) (app t (insert bnds a u'))
        := cong_appᵣ_clos reds' (Insert.attached_after_insert is_attached.attached_is_in)
      RedMany.cons (congAppR is_attached red) ind_hypothesis
