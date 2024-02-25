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
    | termination : Term            -- ⊥
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
    | obj
      : { attrs : List Attr }
      → (bnds : Bindings attrs)
      → AllValue bnds
      → IsValue (obj bnds)
    | termination : IsValue termination

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

namespace IsValue
end IsValue

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

  def attached_is_value
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { a : Attr }
    { t : Term }
    (all_value : AllValue bnds)
    (is_attached : IsAttached a t bnds)
    : IsValue t
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

namespace Context
  def insert
    (i : Nat)
    { attrs : List Attr }
    (bnds : Bindings attrs)
    (ctx : Context)
    : Context
    := match i with
      | 0 => Context.cons bnds ctx
      | Nat.succ n => match ctx with
        | Context.prog p => Context.cons bnds (Context.prog p)
        | Context.cons bindings rest => Context.cons bindings (insert n bnds rest)

  def insert_keeps_prog
    { i : Nat }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { ctx : Context }
    : getProg ctx = getProg (insert i bnds ctx)
    := match i with
      | 0 => by simp [insert, getProg]
      | Nat.succ n => match ctx with
        | Context.prog p => by simp [insert, getProg]
        | Context.cons bindings rest => by
          simp [insert, getProg]
          let hypothesis := @insert_keeps_prog n attrs bnds rest
          exact hypothesis

  -- def insert_keeps_top
  --   { i : Nat }
  --   (gt : i > 0)
  --   { attrs : List Attr }
  --   { bnds : Bindings attrs }
  --   { ctx : Context }
  --   : top ctx = top (insert i bnds ctx)
  --   := match i with
  --     |

end Context


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
      → { ctx : Context }
      → IsValue n
      → IsValue (obj bnds)
      → ReduceCtx
        ctx
        (app (obj bnds) (Bindings.singleton "ρ" n)) -- ⟦ B ⟧(ρ ↦ n)
        (obj (insert bnds "ρ" n)) -- ⟦ ρ ↦ n, B ─ ρ ⟧
    | r10
      : { attrs app_attrs : List Attr }
      → { bnds : Bindings attrs}
      → { app_bnds : Bindings app_attrs}
      → { ctx : Context }
      → { a : Attr }
      → a ∈ attrs
      → a ∈ app_attrs
      → a ≠ "ρ"
      → ReduceCtx
        ctx
        (app (obj bnds) (app_bnds)) -- ⟦ a ↦ t₁, B₁ ⟧(a ↦ t₂, B₂)
        termination                 -- ⊥
    | r11
      : { attrs : List Attr }
      → { bnds : Bindings attrs}
      → { ctx : Context }
      → { a : Attr }
      → a ∉ attrs
      → "φ" ∉ attrs
      -- → "λ" ∉ attrs
      → "ρ" ∈ attrs
      → "σ" ∈ attrs
      → ReduceCtx
        ctx
        (dot (obj bnds) a) -- ⟦ B ⟧.a
        termination        -- ⊥
    | r12
      : { ctx : Context }
      → { a : Attr }
      → ReduceCtx
        ctx
        (dot termination a)
        termination
    | terminationApp
      : { app_attrs : List Attr }
      → { app_bnds : Bindings app_attrs}
      → { ctx : Context }
      → ReduceCtx
        ctx
        (app termination (app_bnds)) -- ⊥(B)
        termination                  -- ⊥
end
open ReduceCtx
-- match on reduction:
-- | congDot red => sorry
-- | congObj is_attached red => _
-- | congAppL red => _
-- | congAppR is_attached red => _
-- | r4 => _
-- | r5 => _
-- | r6 n is_attached is_value => _
-- | r7 for_all void_bnds all_value => _
-- | r8 not_in n is_value is_attached => _
-- | r9 is_value is_value_obj => _
-- | r10 a_in a_in' a_not_ρ => _
-- | r11 a_not_in φ_not_in ρ_in σ_in => _
-- | r12 => _
-- | terminationApp => _

def context_mid_insert
  (i : Nat)
  { ctx : Context }
  { attrs new_attrs : List Attr }
  { bnds : Bindings attrs }
  (new_bnds : Bindings new_attrs)
  { t u : Term }
  (red : ReduceCtx (Context.cons bnds ctx) t u)
  : ReduceCtx (Context.cons bnds (Context.insert i new_bnds ctx)) t u
  := match red with
    | congDot reduction =>
      let hypothesis
        := context_mid_insert i new_bnds reduction
      congDot hypothesis
    | congObj is_attached reduction =>
      let hypothesis := context_mid_insert (i + 1) new_bnds reduction
      congObj is_attached hypothesis
    | congAppL reduction =>
      let hypothesis := context_mid_insert i new_bnds reduction
      congAppL hypothesis
    | congAppR is_attached reduction =>
      let hypothesis := context_mid_insert i new_bnds reduction
      congAppR is_attached hypothesis
    | r4 => by
      let temp := @r4 (Context.cons bnds (Context.insert i new_bnds ctx))
      rw [getProg, ←Context.insert_keeps_prog] at temp
      exact temp
    | r5 => r5
    | r6 n is_attached is_value => r6 n is_attached is_value
    | r7 for_all void_bnds all_value => r7 for_all void_bnds all_value
    | r8 not_in n is_value is_attached => r8 not_in n is_value is_attached
    | r9 is_value is_value_obj => r9 is_value is_value_obj
    | r10 a_in a_in' a_not_ρ => r10 a_in a_in' a_not_ρ
    | r11 a_not_in φ_not_in ρ_in σ_in => r11 a_not_in φ_not_in ρ_in σ_in
    | r12 => r12
    | terminationApp => terminationApp

def context_pumping
  -- (a : Attr)
  { attrs : List Attr }
  (bnds : Bindings attrs)
  { ctx : Context }
  { t u : Term }
  (red : ReduceCtx ctx t u)
  -- : Σ u' : Term, ReduceCtx (Context.cons (remove bnds a) ctx) t u'
  : Σ u' : Term, ReduceCtx (Context.cons bnds ctx) t u'
  := match t with
  | obj bnds' => match red with
    | @congObj a term term' _ _ bindings is_attached reduction =>
      let reduction' := context_mid_insert 0 bnds reduction
      -- let ⟨u', red'⟩ := context_pumping bnds reduction
      -- ReduceCtx (Context.cons bnds ctx) (obj bindings) u'
      -- congObj :: ReduceCtx ctx (obj bnds) (obj (insert bnds a t'))
      ⟨ obj (insert bindings a term')
      , congObj is_attached reduction'
      ⟩
  | app term bnds' => match red with
    | congAppL red_term =>
      let ⟨u', red'⟩ := context_pumping bnds red_term
      ⟨app u' bnds', congAppL red'⟩
    | @r7 _ bindings _ _ for_all void_bnds all_value =>
      ⟨ (obj (remove (insertAll void_bnds bindings) "ν")) -- same as `u`, but inference fails
      , r7 for_all void_bnds all_value
      ⟩
    | @r9 _ bindings n _ is_value is_value_obj =>
      ⟨ (obj (insert bindings "ρ" n)) -- same as `u`, but inference fails
      , r9 is_value is_value_obj
      ⟩
    | r10 a_in a_in' a_not_ρ =>
      ⟨ termination
      , r10 a_in a_in' a_not_ρ
      ⟩
    | terminationApp =>
      ⟨termination, terminationApp⟩
    -- | congAppR _ _=> _
  | dot term a => match red with
    | congDot red_term =>
      let ⟨u', red'⟩ := context_pumping bnds red_term
      ⟨dot u' a, congDot red'⟩
    | r11 c_not_in φ_not_in ρ_in σ_in =>
      ⟨termination, r11 c_not_in φ_not_in ρ_in σ_in⟩
    | r12 =>
      ⟨termination, r12⟩
  | glob => ⟨obj (insert (getProg ctx).snd "σ" glob), r4⟩
  | this => ⟨obj bnds, r5⟩
  | termination => by contradiction


inductive NormalForm : Term → Type where
  | nf
    : { t : Term }
    → ((u : Term) → (ctx : Context) → ReduceCtx ctx t u → False)
    → NormalForm t

inductive AllNormal : { attrs : List Attr } → Bindings attrs → Type where
  | nil : AllNormal Bindings.nil
  | cons
    : { attrs : List Attr }
    → { bnds : Bindings attrs }
    → { a : Attr }
    → (not_in : a ∉ attrs)
    → { t : Term }
    → NormalForm t
    → AllNormal bnds
    → AllNormal (Bindings.cons not_in (some t) bnds)

namespace NormalForm
  def glob_not_nf
    : NormalForm glob → False
    | NormalForm.nf f =>
      let ctx := Context.prog Bindings.nil
      let u := obj (insert (getProg ctx).snd "σ" glob)
      let red := @r4 ctx
      let false := f u ctx red
      by contradiction

  def this_not_nf
    : NormalForm this → False
    | NormalForm.nf f =>
      let ctx := Context.prog Bindings.nil
      let u := obj (top ctx).snd
      let red := @r5 ctx
      let false := f u ctx red
      by contradiction

  def obj_subterm_nf
    { attrs : List Attr }
    { bnds : Bindings attrs }
    { a : Attr }
    { t : Term }
    (is_attached : IsAttached a t bnds)
    (nf : NormalForm (obj bnds))
    : NormalForm t
    := match nf with
      | NormalForm.nf f => NormalForm.nf λ _ ctx red =>
        let ⟨u', red'⟩ := context_pumping ((remove bnds a)) red
        f
          (obj (insert bnds a u'))
          ctx
          (congObj is_attached red')

  def dot_subterm_nf
    { t : Term }
    { a : Attr }
    (nf : NormalForm (dot t a))
    : NormalForm t
    := match nf with
    | NormalForm.nf f => NormalForm.nf λ u ctx red =>
      f (dot u a) ctx (congDot red)

  def app_subterm_nf
    { t : Term }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    (nf : NormalForm (app t bnds))
    : NormalForm t
    := match nf with
    | NormalForm.nf f => NormalForm.nf λ u ctx red =>
      f (app u bnds) ctx (congAppL red)

mutual


  def dot_not_nf
    { t : Term }
    { a : Attr }
    (nf_t : NormalForm t)
    : NormalForm (dot t a) → False
    | NormalForm.nf f => match nf_t with | NormalForm.nf f_t => match t with
      | obj bnds => sorry
      | app term bnds => app_not_nf (app_subterm_nf nf_t) nf_t
      | dot term a => dot_not_nf (dot_subterm_nf nf_t) nf_t
      | glob => glob_not_nf nf_t
      | this => this_not_nf nf_t
      | termination =>
        let ctx := Context.prog Bindings.nil
        f termination ctx r12

  def app_not_nf
    { t : Term }
    { attrs : List Attr }
    { bnds : Bindings attrs }
    (nf_t : NormalForm t)
    : NormalForm (app t bnds) → False
    | NormalForm.nf f => match nf_t with | NormalForm.nf f_t => match t with
      | obj bnds => sorry
      | app term bnds => app_not_nf (app_subterm_nf nf_t) nf_t
      | dot term a => dot_not_nf (dot_subterm_nf nf_t) nf_t
      | glob => glob_not_nf nf_t
      | this => this_not_nf nf_t
      | termination =>
        let ctx := Context.prog Bindings.nil
        f termination ctx terminationApp
end
decreasing_by sorry


end NormalForm

def nf_is_value
  { t : Term }
  (nf : NormalForm t)
  : IsValue t
  := match nf with
    | NormalForm.nf f => match t with
      | obj bnds => sorry
      | app term bnds => sorry
      | dot term a =>
        let term_nf := NormalForm.dot_subterm_nf nf
        let hypothesis := nf_is_value term_nf
        sorry
      | glob =>
        let ctx := Context.prog Bindings.nil
        let u := obj (insert (getProg ctx).snd "σ" glob)
        let red := @r4 ctx
        let false := f u ctx red
        by contradiction
      | this =>
        let ctx := Context.prog Bindings.nil
        let u := obj (top ctx).snd
        let red := @r5 ctx
        let false := f u ctx red
        by contradiction
      | termination => IsValue.termination

def value_is_nf
  { t : Term }
  (is_value : IsValue t)
  : NormalForm t
  := match t with
    | @obj attrs bnds => match is_value with
      | IsValue.obj _ all_value => NormalForm.nf λ u ctx red => match red with
        | @congObj a term term' ctx _ bnds is_attached reduction =>
          let term_is_value
            : IsValue term
            := IsAttached.attached_is_value all_value is_attached
          let (NormalForm.nf f)
            : NormalForm term
            := value_is_nf term_is_value
          f term' ((Context.cons (remove bnds a) ctx)) reduction
    | termination => match is_value with
      | IsValue.termination => NormalForm.nf λ u ctx red => by contradiction
decreasing_by sorry

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
