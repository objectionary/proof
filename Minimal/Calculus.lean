set_option autoImplicit false

@[reducible]
def Attr := String

mutual
  inductive OptionalAttr where
    | attached : Term → OptionalAttr
    | void : OptionalAttr

  inductive AttrList : List Attr → Type where
    | nil : AttrList []
    | cons
      : { lst : List Attr }
      → (a : Attr)
      → a ∉ lst
      → OptionalAttr
      → AttrList lst
      → AttrList (a :: lst)

  inductive Term : Type where
    | loc : Nat → Term
    | dot : Term → Attr → Term
    | app : Term → Attr → Term → Term
    -- | obj : (List (Attr × OptionalAttr)) → Term
    | obj : { lst : List Attr } → AttrList lst → Term
end
open OptionalAttr
open Term

def mapAttrList : (Term → Term) → { lst : List Attr } → AttrList lst → AttrList lst
  := λ f _ alst =>
    let f' := λ optional_attr => match optional_attr with
      | void => void
      | attached x => attached (f x)
    match alst with
    | AttrList.nil => AttrList.nil
    | AttrList.cons a not_in opAttr attrLst =>
        AttrList.cons a not_in (f' opAttr) (mapAttrList f attrLst)

partial def incLocatorsFrom (k : Nat) (term : Term) : Term
  := match term with
    | loc n => if n ≥ k then loc (n+1) else loc n
    | dot t a => dot (incLocatorsFrom k t) a
    | app t a u => app (incLocatorsFrom k t) a (incLocatorsFrom k u)
    | obj o => (obj (mapAttrList (incLocatorsFrom (k+1)) o))

partial def incLocators : Term → Term
  := incLocatorsFrom 0

partial def substituteLocator : Int × Term → Term → Term
  := λ (k, v) term => match term with
    | obj o => obj (mapAttrList (substituteLocator (k + 1, incLocators v)) o)
    | dot t a => dot (substituteLocator (k, v) t) a
    | app t a u => app (substituteLocator (k, v) t) a (substituteLocator (k, v) u)
    | loc n =>
      if (n < k) then (loc n)
      else if (n == k) then v
      else loc (n-1)

def lookup { lst : List Attr } (l : AttrList lst) (a : Attr) : Option OptionalAttr
  := match l with
    | AttrList.nil => none
    | AttrList.cons name _ opAttr tail =>
        if (name == a) then some opAttr
        else lookup tail a

def insert
  { lst : List Attr }
  (l : AttrList lst)
  (a : Attr)
  (u : OptionalAttr)
  : (AttrList lst)
  := match l with
    | AttrList.nil => AttrList.nil
    | AttrList.cons name not_in opAttr tail =>
        if name == a then AttrList.cons name not_in u tail
        else AttrList.cons name not_in opAttr (insert tail a u)

def insertMany
  { lst lstNew : List Attr }
  (l : AttrList lst)
  (newAttrs : AttrList lstNew)
  : AttrList lst
  := match newAttrs with
    | AttrList.nil => l
    | AttrList.cons name _ opAttr tail =>
        insertMany (insert l name opAttr) tail

def insertAll
  { lst : List Attr }
  (l : AttrList lst)
  (newAttrs : AttrList lst)
  : AttrList lst
  := match (l, newAttrs) with
    | (AttrList.nil, AttrList.nil) => AttrList.nil
    | (AttrList.cons a not_in _ tail1, AttrList.cons _ _ opAttr tail2) =>
        AttrList.cons a not_in opAttr (insertAll tail1 tail2)

-- Contains proofs on properties of insertions
namespace Insert
  open AttrList

  def insertEmpty
    { a : Attr }
    { u : OptionalAttr }
    : insert nil a u = nil
    := by rfl

  def insertManyIdentity
    { lst : List Attr }
    { l : AttrList lst }
    : insertMany l nil = l
    := by rw [insertMany]

  def insertManyEmpty
    { lst : List Attr }
    (l : AttrList lst)
    : insertMany nil l = nil
    := match l with
      | nil => insertManyIdentity
      | cons _ _ _ tail => insertManyEmpty tail

  def insertAllSelf
    { lst : List Attr }
    (l : AttrList lst)
    : insertAll l l = l
    := match l with
      | nil => by rfl
      | cons a not_in op_attr tail => congrArg (cons a not_in op_attr) (insertAllSelf tail)
end Insert

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
  | obj o => obj (mapAttrList nf o)
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
  | is_attr
    : { lst : List Attr }
    → (a : Attr)
    → a ∈ lst
    → (l : AttrList lst)
    → IsAttr a (obj l)

inductive IsAttached : Attr → Term → Term → Type where
  | zeroth_attached
    : { lst : List Attr }
    → (a : Attr)
    → (not_in : a ∉ lst)
    → (t : Term)
    → (l : AttrList lst)
    → IsAttached a t (obj (AttrList.cons a not_in (attached t) l))
  | next_attached
    : { lst : List Attr }
    → (a : Attr)
    → (t : Term)
    → (l : AttrList lst)
    → (b : Attr)
    → (a ≠ b)
    → (not_in : b ∉ lst)
    → (u : OptionalAttr)
    → IsAttached a t (obj l)
    → IsAttached a t (obj (AttrList.cons b not_in u l))

namespace Insert
  def insertAttachedStep
    { a b : Attr }
    { neq : a ≠ b }
    { t : Term }
    { lst : List Attr }
    { not_in : b ∉ lst }
    { u : OptionalAttr }
    { l : AttrList lst }
    (_ : IsAttached a t (obj l))
    : insert (AttrList.cons b not_in u l) a (attached t)
        = AttrList.cons b not_in u (insert l a (attached t))
    := by simp [insert, neq];
          split
          . have neq' := neq.symm
            contradiction
          . simp

  def insertAttached
    { a : Attr }
    { t : Term }
    { lst : List Attr }
    { l : AttrList lst }
    : IsAttached a t (obj l)
    → insert l a (attached t) = l
      | IsAttached.zeroth_attached _ _ _ _ => by simp [insert]
      | IsAttached.next_attached _ _ l b neq not_in u isAttached =>
          let step := @insertAttachedStep a b neq t _ not_in u _ isAttached
          Eq.trans step (congrArg (AttrList.cons b not_in u) (insertAttached isAttached))
end Insert

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

  -- def size : {t t' : Term} → Reduce t t' → Nat
  --   | _, _, .congOBJ t t' b lst red eq => 1 + size red
  --   | _, _, .congDOT t t' a red => 1 + size red
  --   | _, _, .congAPPₗ t t' u a red => 1 + size red
  --   | _, _, .congAPPᵣ t u u' a red => 1 + size red
  --   | _, _, .dot_c t t_c c lst eq lookup_eq => 1
  --   | _, _, .dot_cφ t c lst eq lookup_c isAttr_φ => 1
  --   | _, _, .app_c t u c lst eq lookup_eq => 1

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
  mutual
    inductive Premise : { lst : List Attr } → (l1 : AttrList lst) → (l2 : AttrList lst) → Type where
      | nil : Premise AttrList.nil AttrList.nil
      | consVoid
        : (a : Attr)
        → { lst : List Attr }
        → { l1 : AttrList lst }
        → { l2 : AttrList lst }
        → { not_in : a ∉ lst }
        → Premise l1 l2
        → Premise (AttrList.cons a not_in void l1) (AttrList.cons a not_in void l2)
      | consAttached
        : (a : Attr)
        → (t1 : Term)
        → (t2 : Term)
        → PReduce t1 t2
        → { lst : List Attr }
        → { l1 : AttrList lst }
        → { l2 : AttrList lst }
        → { not_in : a ∉ lst }
        → Premise l1 l2
        → Premise (AttrList.cons a not_in (attached t1) l1) (AttrList.cons a not_in (attached t2) l2)

    inductive PReduce : Term → Term → Type where
      | pcongOBJ
        : { lst : List Attr }
        → (l : AttrList lst)
        → (newAttrs : AttrList lst)
        → Premise l newAttrs
        → PReduce (obj l) (obj (insertAll l newAttrs))
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
  end

  mutual
    def reflexivePremise
      { lst : List Attr }
      (l : AttrList lst)
      : Premise l l
      := match l with
        | AttrList.nil => Premise.nil
        | AttrList.cons name not_in opAttr tail =>
            match opAttr with
              | void => Premise.consVoid name (reflexivePremise tail)
              | attached t => Premise.consAttached name t t (prefl t) (reflexivePremise tail)

    def prefl : (t : Term) → PReduce t t
      := λ term => match term with
        | loc n => PReduce.pcong_ρ n
        | dot t a => PReduce.pcongDOT t t a (prefl t)
        | app t a u => PReduce.pcongAPP t t u u a (prefl t) (prefl u)
        | @obj lst l =>
            let premise := reflexivePremise l
            by  have simplifier
                    : PReduce (obj l) (obj (insertAll l l)) = PReduce (obj l) (obj l)
                    := congrArg (λ x => PReduce (obj l) (obj x)) (Insert.insertAllSelf l)
                have proof := PReduce.pcongOBJ l l premise
                exact Eq.mp simplifier proof
  end
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
  | _, _, .congOBJ t t' b l red eq =>
      .pcongOBJ
        l
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

-- app_c
--       : ∀ t u c lst
--       , t = obj lst
--       → lookup lst c = some void
--       → Reduce (app t c u) (obj (insert lst c (attached (incLocators u))))

def clos_trans : { t t' t'' : Term } → (t ⇝* t') → (t' ⇝* t'') → (t ⇝* t'')
  | _, _, _, RedMany.nil, reds => reds
  | _, _, _, RedMany.cons lm mn_many, reds => RedMany.cons lm (clos_trans mn_many reds)

-- def congOBJClos
  -- { t t' : Term }
  -- { b : Attr }
  -- { lst : List Attr }
  -- { l : AttrList lst }
  -- : (t ⇝* t')
  -- → IsAttached b t (obj l)
  -- → (obj l ⇝* obj (insert l b (attached t')))
  -- := λ r a => match r with
    -- | RedMany.nil => _
    -- | RedMany.cons red redMany => _

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
