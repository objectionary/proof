set_option autoImplicit false

@[reducible]
def Attr := String

mutual
  inductive OptionalAttr where
    | attached : Term → OptionalAttr
    | void : OptionalAttr

  inductive Bindings : List Attr → Type where
    | nil : Bindings []
    | cons
      : { lst : List Attr }
      → (a : Attr)
      → a ∉ lst
      → OptionalAttr
      → Bindings lst
      → Bindings (a :: lst)

  inductive Term : Type where
    | obj : { lst : List Attr } → Bindings lst → Term
    | dot : Term → Attr → Term
    | app : Term → Attr → Term → Term
    | ξ   : Term
    | Φ   : Term
end
open OptionalAttr
open Term


-- def substitute (tξ : Term) (tΦ : Term) : Term → Term
--   | obj o => obj o
--   | dot t a => dot (substitute tξ tΦ t) a
--   | app t a u => app (substitute tξ tΦ t) a (substitute tξ tΦ u)
--   | ξ => tξ
--   | Φ => tΦ

def substitute (tξ : Term) : Term → Term
  | obj o => obj o
  | dot t a => dot (substitute tξ t) a
  | app t a u => app (substitute tξ t) a (substitute tξ u)
  | ξ => tξ
  | Φ => Φ

def lookup { lst : List Attr } (l : Bindings lst) (a : Attr)
  : Option OptionalAttr
  := match l with
    | Bindings.nil => none
    | Bindings.cons name _ opAttr tail =>
        if (name == a) then some opAttr
        else lookup tail a

def insert
  { lst : List Attr }
  (l : Bindings lst)
  (a : Attr)
  (u : OptionalAttr)
  : (Bindings lst)
  := match l with
    | Bindings.nil => Bindings.nil
    | Bindings.cons name not_in opAttr tail =>
        if name == a then Bindings.cons name not_in u tail
        else Bindings.cons name not_in opAttr (insert tail a u)

def has_no_void_attrs { lst : List Attr } : Bindings lst → Bool
  | Bindings.nil => true
  | Bindings.cons _ _ u tail => match u with
    | void => false
    | attached _ => has_no_void_attrs tail

@[reducible]
def Context := Term

inductive Reduce : Context → Term → Term → Type where
  | congOBJ
    : { a : Attr }
    → { t t' : Term }
    → { attrs : List Attr }
    → { bnds : Bindings attrs }
    → { ctx : Context }
    → has_no_void_attrs bnds
    → lookup bnds a = some (attached t)
    → Reduce ctx t t'
    → Reduce ctx
      (obj bnds)
      (obj (insert bnds a (attached t')))
  | congDOT
    : { a : Attr }
    → { t t' : Term }
    → { ctx : Context }
    → Reduce ctx t t'
    → Reduce ctx (dot t a) (dot t' a)
  | congAPPₗ
    : { a : Attr }
    → { t t' u : Term }
    → { ctx : Context }
    → Reduce ctx t t'
    → Reduce ctx (app t a u) (app t' a u)
  | congAPPᵣ
    : { a : Attr }
    → { t u u' : Term }
    → { ctx : Context }
    → Reduce ctx u u'
    → Reduce ctx (app t a u) (app t a u')
  | dot_c
    : (ctx : Context)
    → (t : Term)
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → lookup l c = some (attached t)
    → Reduce ctx
      (dot (obj l) c)
      (app (substitute (obj l) t) "ρ" ξ)
  | dot_ρ
    : (ctx : Context)
    → (t : Term)
    → { lst : List Attr }
    → (l : Bindings lst)
    → lookup l "ρ" = some (attached t)
    → Reduce ctx
      (dot (obj l) "ρ")
      (substitute (obj l) t)
  | dot_φ
    : (ctx : Context)
    → (c : Attr)
    → (tφ : Term)
    → { lst : List Attr }
    → (l : Bindings lst)
    → lookup l c = none
    → lookup l "φ" = some (attached tφ)
    → Reduce ctx
      (dot (obj l) c)
      (dot (app (substitute (obj l) tφ) "ρ" ξ) c)
  | dot_Φ
    : (a : Attr)
    → (t_a : Term)
    → { lst : List Attr }
    → (l : Bindings lst)
    → lookup l a = some (attached t_a)
    → Reduce (obj l)
      (dot Φ a)
      (app (substitute (obj l) t_a) "ρ" Φ)
  | app_c
    : (ctx : Context)
    → (u : Term)
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → lookup l c = some void
    → Reduce ctx
      (app (obj l) c u)
      (obj (insert l c (attached u)))
  | app_ρ
    : (ctx : Context)
    → (u : Term)
    → { lst : List Attr }
    → (l : Bindings lst)
    → lookup l "ρ" = some _
    → Reduce ctx
      (app (obj l) "ρ" u)
      (obj (insert l "ρ" (attached u)))
