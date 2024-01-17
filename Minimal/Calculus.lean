set_option autoImplicit false

@[reducible]
def Attr := String

mutual
  inductive OptionalAttr where
    | attached : Term → OptionalAttr
    | void : OptionalAttr

  inductive Term : Type where
    | loc : Nat → Term
    | dot : Term → Attr → Term
    | app : Term → Attr → Term → Term
    | obj : (List (Attr × OptionalAttr)) → Term
end
open OptionalAttr
open Term


def mapObj : (Term → Term) → (List (Attr × OptionalAttr)) → (List (Attr × OptionalAttr))
  := λ f o =>
  let f' := λ (attr_name, attr_body) =>
      match attr_body with
        | void => (attr_name, void)
        | attached x => (attr_name, attached (f x))
  (f' <$> o)

partial def incLocatorsFrom (k : Nat) (term : Term) : Term
  := match term with
    | loc n => if n ≥ k then loc (n+1) else loc n
    | dot t a => dot (incLocatorsFrom k t) a
    | app t a u => app (incLocatorsFrom k t) a (incLocatorsFrom k u)
    | obj o => (obj (mapObj (incLocatorsFrom (k+1)) o))

partial def incLocators : Term → Term
  := incLocatorsFrom 0

partial def substituteLocator : Int × Term → Term → Term
  := λ (k, v) term => match term with
    | obj o => obj (mapObj (substituteLocator (k + 1, incLocators v)) o)
    | dot t a => dot (substituteLocator (k, v) t) a
    | app t a u => app (substituteLocator (k, v) t) a (substituteLocator (k, v) u)
    | loc n =>
      if (n < k) then (loc n)
      else if (n == k) then v
      else loc (n-1)

def lookup (l : List (Attr × OptionalAttr)) (a : Attr) : Option OptionalAttr
  := match l with
    | [] => none
    | List.cons (name, term) tail =>
        if (name == a) then some term
        else lookup tail a

def insert (l : List (Attr × OptionalAttr)) (a : Attr) (u : OptionalAttr) : (List (Attr × OptionalAttr))
  := match l with
    | [] => []
    | List.cons (name, term) tail =>
        if (name == a) then List.cons (name, u) tail
        else List.cons (name, term) (insert tail a u)

def insertMany : List (Attr × OptionalAttr) → List (Attr × OptionalAttr) → List (Attr × OptionalAttr)
  := λ lst newAttrs => match newAttrs with
    | [] => lst
    | List.cons (attr, term) tail =>
        insertMany (insert lst attr term) tail

def insertEmpty { a : Attr } { u : OptionalAttr } : insert [] a u = []
  := by rfl
def insertManyIdentity : { l : List (Attr × OptionalAttr) } → insertMany l [] = l
  := by intro l
        rw [insertMany]
def insertManyEmpty : (lst : List (Attr × OptionalAttr)) → insertMany [] lst = []
  := λ l => match l with
    | [] => insertManyIdentity
    | _ :: xs => insertManyEmpty xs

partial def whnf : Term → Term
  | loc n => loc n
  | obj o => obj o
  | app t a u => match (whnf t) with
    | obj o => match lookup o a with
      | none => app (obj o) a u
      | some (attached _) => app (obj o) a u
      | some void => obj (insert o a (attached (incLocators u)))
    | t' => app t' a u
  | dot t a => match (whnf t) with
    | obj o => match lookup o a with
      | some (attached u) => whnf (substituteLocator (0, obj o) u)
      | some void => dot (obj o) a
      | none => match lookup o "φ" with
        | some _ => dot (dot (obj o) "φ") a
        | none => dot (obj o) a
    | t' => dot t' a

partial def nf : Term → Term
  | loc n => loc n
  | obj o => obj (mapObj nf o)
  | app t a u => match (whnf t) with
    | obj o => match lookup o a with
      | none => app (nf (obj o)) a (nf u)
      | some (attached _) => app (nf (obj o)) a (nf u)
      | some void => nf (obj (insert o a (attached (incLocators u))))
    | t' => app (nf t') a (nf u)
  | dot t a => match (whnf t) with
    | obj o => match lookup o a with
      | some (attached u) => nf (substituteLocator (0, obj o) u)
      | some void => dot (nf (obj o)) a
      | none => match lookup o "φ" with
        | some _ => nf (dot (dot (obj o) "φ") a)
        | none => dot (nf (obj o)) a
    | t' => dot (nf t') a

inductive IsAttr : Attr → Term → Type where
  | zeroth_attr
    : (a : Attr)
    → (lst : List (Attr × OptionalAttr))
    → IsAttr a (obj ((a, _) :: lst))
  | next_attr
    : (a : Attr)
    → (lst : List (Attr × OptionalAttr))
    → IsAttr a (obj lst)
    → IsAttr a (obj ((_, _) :: lst))

inductive IsAttached : Attr → Term → Term → Type where
  | zeroth_attached
    : { lst : List (Attr × OptionalAttr)}
    → (a : Attr)
    → (t : Term)
    → IsAttached a t (obj ((a, attached t) :: lst))
  | next_attached
    : { lst : List (Attr × OptionalAttr)}
    → (a : Attr)
    → (t : Term)
    → IsAttached a t (obj lst)
    → IsAttached a t (obj ((_, _) :: lst))

def insertAttached
  { a : Attr }
  { t : Term }
  { lst : List (Attr × OptionalAttr) }
  : IsAttached a t (obj lst)
  → insert lst a (attached t) = lst
  -- := λ isAttached => match isAttached with
    | IsAttached.zeroth_attached _ _ => by simp [insert]
    | IsAttached.next_attached _ _ isAttached => match lst with
      | [] => _ -- by contradiction
      | _ :: xs => _


namespace Reduce

  inductive Reduce : Term → Term → Type where
    | congOBJ
      : ∀ t t' b lst
      , Reduce t t'
      → IsAttached b t (obj lst)
      → Reduce (obj lst) (obj (insert lst b (attached t')))
    | congDOT : ∀ t t' a, Reduce t t' → Reduce (dot t a) (dot t' a)
    | congAPPₗ : ∀ t t' u a, Reduce t t' → Reduce (app t a u) (app t' a u)
    | congAPPᵣ : ∀ t u u' a, Reduce u u' → Reduce (app t a u) (app t a u')
    | dot_c
      : ∀ t t_c c lst
      , t = obj lst
      → lookup lst c = some (attached t_c)
      → Reduce (dot t c) (substituteLocator (0, t) t_c)
    | dot_cφ
      : ∀ t c lst
      , t = obj lst
      → lookup lst c = none
      → IsAttr "φ" t
      → Reduce (dot t c) (dot (dot t "φ") c)
    | app_c
      : ∀ t u c lst
      , t = obj lst
      → lookup lst c = some void
      → Reduce (app t c u) (obj (insert lst c (attached (incLocators u))))

  def size : {t t' : Term} → Reduce t t' → Nat
    | _, _, .congOBJ t t' b lst red eq => 1 + size red
    | _, _, .congDOT t t' a red => 1 + size red
    | _, _, .congAPPₗ t t' u a red => 1 + size red
    | _, _, .congAPPᵣ t u u' a red => 1 + size red
    | _, _, .dot_c t t_c c lst eq lookup_eq => 1
    | _, _, .dot_cφ t c lst eq lookup_c isAttr_φ => 1
    | _, _, .app_c t u c lst eq lookup_eq => 1

open Reduce

inductive ForAll : {a : Type} → (a → Type) → List a → Type where
  | triv : ∀ f, ForAll f []
  | step
    : ∀ a f lst
    , ForAll f lst
    → (x : a)
    → f x
    → ForAll f (x :: lst)

namespace PReduce
  inductive PReduce : Term → Term → Type where
    | pcongOBJ
      : ∀ lst
      , (premise : List (Attr × Term × Term))
      → ForAll (λ (_, ti, ti') => PReduce ti ti') premise
      → ForAll (λ (a, ti, _) => IsAttached a ti (obj lst)) premise
      → PReduce (obj lst) (obj (insertMany lst (List.map (λ (a, _, ti') => (a, attached ti')) premise)))
    | pcong_ρ : ∀ n, PReduce (loc n) (loc n)
    | pcongDOT : ∀ t t' a, PReduce t t' → PReduce (dot t a) (dot t' a)
    | pcongAPP : ∀ t t' u u' a, PReduce t t' → PReduce u u' → PReduce (app t a u) (app t' a u')
    | pdot_c
      : ∀ t t' t_c c lst
      , PReduce t t'
      → t' = obj lst
      → lookup lst c = some (attached t_c)
      → PReduce (dot t c) (substituteLocator (0, t') t_c)
    | pdot_cφ
      : ∀ t t' c lst
      , PReduce t t'
      → t' = obj lst
      → lookup lst c = none
      → IsAttr "φ" t'
      → PReduce (dot t c) (dot (dot t' "φ") c)
    | papp_c
      : ∀ t t' u u' c lst
      , PReduce t t'
      → PReduce u u'
      → t' = obj lst
      → lookup lst c = some void
      → PReduce (app t c u) (obj (insert lst c (attached (incLocators u'))))

  def prefl : (t : Term) → PReduce t t
    := λ term => match term with
      | loc n => PReduce.pcong_ρ n
      | dot t a => PReduce.pcongDOT t t a (prefl t)
      | app t a u => PReduce.pcongAPP t t u u a (prefl t) (prefl u)
      | obj lst => PReduce.pcongOBJ
          lst
          []
          (ForAll.triv _)
          (ForAll.triv _)
open PReduce


inductive RedMany : Term → Term → Type where
  | nil : { m : Term } → RedMany m m
  | cons : { l m n : Term} → Reduce l m → RedMany m n → RedMany l n

inductive ParMany : Term → Term → Type where
  | nil : { m : Term } → ParMany m m
  | cons : { l m n : Term} → PReduce l m → ParMany m n → ParMany l n

scoped infix:20 " ⇝ " => Reduce
scoped infix:20 " ⇛ " => PReduce
scoped infix:20 " ⇝* " => RedMany
scoped infix:20 " ⇛* " => RedMany

def reg_to_par : {t t' : Term} → (t ⇝ t') → (t ⇛ t')
  | _, _, .congOBJ t t' b lst red eq =>
      .pcongOBJ
        lst
        [(b, t, t')]
        (ForAll.step (Attr × Term × Term) _ [] (ForAll.triv _) _ (reg_to_par red))
        (ForAll.step (Attr × Term × Term) _ [] (ForAll.triv _) _ eq)
  | _, _, .congDOT t t' a red =>
      .pcongDOT t t' a (reg_to_par red)
  | _, _, .congAPPₗ t t' u a red =>
      .pcongAPP t t' u u a (reg_to_par red) (prefl u)
  | _, _, .congAPPᵣ t u u' a red =>
      .pcongAPP t t u u' a (prefl t) (reg_to_par red)
  | _, _, .dot_c t t_c c lst eq lookup_eq =>
      .pdot_c t t t_c c lst (prefl t) eq lookup_eq
  | _, _, .dot_cφ t c lst eq lookup_c isAttr_φ =>
      .pdot_cφ t t c lst (prefl t) eq lookup_c isAttr_φ
  | _, _, .app_c t u c lst eq lookup_eq =>
      .papp_c t t u u c lst (prefl t) (prefl u) eq lookup_eq


def clos_trans : { t t' t'' : Term } → (t ⇝* t') → (t' ⇝* t'') → (t ⇝* t'')
  | _, _, _, RedMany.nil, reds => reds
  | _, _, _, RedMany.cons lm mn_many, reds => RedMany.cons lm (clos_trans mn_many reds)

-- | congOBJ
      -- : ∀ t t' b lst
      -- , Reduce t t'
      -- → IsAttached b t (obj lst)
      -- → Reduce (obj lst) (obj (insert lst b (attached t')))
def confOBJClos
  { t t' : Term }
  { b : Attr }
  { lst : List (Attr × OptionalAttr) }
  : (t ⇝* t')
  → IsAttached b t (obj lst)
  → RedMany (obj lst) (obj (insert lst b (attached t')))
  := λ r a => match r with
    | RedMany.nil => _
    | RedMany.cons red redMany => _

def congDotClos : { t t' : Term } → { a : Attr } → (t ⇝* t') → ((dot t a) ⇝* (dot t' a))
  | _, _, _, RedMany.nil => RedMany.nil
  | _, _, a, @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congDOT l m a lm) (congDotClos mn_many)

def congAPPₗClos : { t t' u : Term } → { a : Attr } → (t ⇝* t') → ((app t a u) ⇝* (app t' a u))
  | _, _, _, _, RedMany.nil => RedMany.nil
  | _, _, u, a, @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congAPPₗ l m u a lm) (congAPPₗClos mn_many)

def congAPPᵣClos : { t u u' : Term } → { a : Attr } → (u ⇝* u') → ((app t a u) ⇝* (app t a u'))
  | _, _, _, _, RedMany.nil => RedMany.nil
  | t, _, _, a, @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congAPPᵣ t l m a lm) (congAPPᵣClos mn_many)

def par_to_redMany : {t t' : Term} → (t ⇛ t') → (t ⇝* t')
  | _, _, .pcongOBJ lst premise f f' => match lst with
    | [] => Eq.ndrec (@RedMany.nil (obj [])) (congrArg obj (Eq.symm (insertManyEmpty _)))
    | a :: b => _
  | _, _, .pcong_ρ n => RedMany.nil
  | _, _, .pcongDOT t t' a prtt' => congDotClos (par_to_redMany prtt')
  | _, _, .pcongAPP t t' u u' a prtt' pruu' => clos_trans
    (congAPPₗClos (par_to_redMany prtt'))
    (congAPPᵣClos (par_to_redMany pruu'))
  | _, _, .pdot_c t t' t_c c lst prtt' path_t'_obj_lst path_lst_c_tc =>
    have tc_t'c_many := congDotClos (par_to_redMany prtt')
    have tc_dispatch := dot_c t' t_c c lst path_t'_obj_lst path_lst_c_tc
    have tc_dispatch_clos := RedMany.cons tc_dispatch RedMany.nil
    clos_trans tc_t'c_many tc_dispatch_clos
  | _, _, .pdot_cφ t t' c lst prtt' path_t'_obj_lst path_lst_c_none isattr_φ_t =>
    have tc_t'c_many := congDotClos (par_to_redMany prtt')
    have tφc_dispatch := dot_cφ t' c lst path_t'_obj_lst path_lst_c_none isattr_φ_t
    have tφc_dispatch_clos := RedMany.cons tφc_dispatch RedMany.nil
    clos_trans tc_t'c_many tφc_dispatch_clos
  | _, _, .papp_c t t' u u' c lst prtt' pruu' path_t'_obj_lst path_lst_c_void =>
    have tu_t'u_many := congAPPₗClos (par_to_redMany prtt')
    have t'u_t'u'_many := congAPPᵣClos (par_to_redMany pruu')
    have tu_t'u'_many := clos_trans tu_t'u_many t'u_t'u'_many
    have tu_app := app_c t' u' c lst path_t'_obj_lst path_lst_c_void
    have tu_app_clos := RedMany.cons tu_app RedMany.nil
    clos_trans tu_t'u'_many tu_app_clos
