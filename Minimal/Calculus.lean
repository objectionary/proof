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

partial def incLocatorsFrom : Nat → Term → Term
  := λ k term => match term with
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

-- def checkUniqueAttributes : (List (Attr × OptionalAttr)) → Bool
--   | _ => true

def lookup : (List (Attr × OptionalAttr)) → Attr → Option OptionalAttr
  := λ l a => match l with
    | [] => none
    | List.cons (name, term) tail =>
        if (name == a) then some term
        else lookup tail a

def insert : (List (Attr × OptionalAttr)) → Attr → OptionalAttr → (List (Attr × OptionalAttr))
  := λ l a u => match l with
    | [] => []
    | List.cons (name, term) tail =>
        if (name == a) then List.cons (name, u) tail
        else List.cons (name, term) (insert tail a u)

def insertMany : (List (Attr × OptionalAttr)) → List (Attr × OptionalAttr) → (List (Attr × OptionalAttr))
  := λ old new => match new with
    | [] => old
    | List.cons (attr, term) tail =>
        insertMany (insert old attr term) tail

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

inductive IsAttr : Attr → Term → Prop where
  | zeroth
    : (a : Attr)
    -- → (t : OptionalAttr)
    → (lst : List (Attr × OptionalAttr))
    → IsAttr a (obj ((a, _) :: lst))
  | after
    : (a : Attr)
    -- → (t : OptionalAttr)
    → (lst : List (Attr × OptionalAttr))
    → IsAttr a (obj lst)
    → IsAttr a (obj ((_, _) :: lst))

namespace Reduce

  inductive Reduce : Term → Term → Type where
    | congOBJ
      : ∀ t t' b lst
      , Reduce t t'
      → lookup lst b = some (attached t)
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
      -- → lookup lst "φ" = some _
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


inductive ForAll : {a : Type} → (a → Prop) → List a → Prop where
  | triv : ∀ f, ForAll f []
  | step
    : ∀ a f lst
    , ForAll f lst
    → (x : a)
    → f x
    → ForAll f (x :: lst)

inductive PReduce : Term → Term → Prop where
  | pcongOBJ
    : ∀ lst
    , (premise : List (Attr × Term × Term))
    → ForAll (λ (_, ti, ti') => PReduce ti ti') premise
    → ForAll (λ (a, ti, _) => lookup lst a = some (attached ti)) premise
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
    -- → lookup lst "φ" = some _
    → IsAttr "φ" t
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

def reg_to_par : {t t' : Term} → Reduce t t' → PReduce t t'
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
