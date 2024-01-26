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

def incLocatorsFrom (n : Nat) (term : Term) : Term
  := match term with
    | loc m => if m < n then loc m else loc (m + 1)
    | dot t a => dot (incLocatorsFrom n t) a
    | app t a u => app (incLocatorsFrom n t) a (incLocatorsFrom n u)
    | obj o => (obj (mapAttrList (incLocatorsFrom (n+1)) o))
decreasing_by sorry

def incLocators : Term → Term
  := incLocatorsFrom 0

def substitute : Nat × Term → Term → Term
  := λ (k, v) term => match term with
    | obj o => obj (mapAttrList (substitute (k + 1, incLocators v)) o)
    | dot t a => dot (substitute (k, v) t) a
    | app t a u => app (substitute (k, v) t) a (substitute (k, v) u)
    | loc n =>
      if (n < k) then (loc n)
      else if (n == k) then v
      else loc (n-1)
decreasing_by sorry

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
      | some (attached u) => whnf (substitute (0, obj o) u)
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
      | some (attached u) => nf (substitute (0, obj o) u)
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

inductive IsAttached : { lst : List Attr } → Attr → Term → AttrList lst → Type where
  | zeroth_attached
    : { lst : List Attr }
    → (a : Attr)
    → (not_in : a ∉ lst)
    → (t : Term)
    → (l : AttrList lst)
    → IsAttached a t (AttrList.cons a not_in (attached t) l)
  | next_attached
    : { lst : List Attr }
    → (a : Attr)
    → (t : Term)
    → (l : AttrList lst)
    → (b : Attr)
    → (a ≠ b)
    → (not_in : b ∉ lst)
    → (u : OptionalAttr)
    → IsAttached a t l
    → IsAttached a t (AttrList.cons b not_in u l)

def isAttachedIsIn
  { lst : List Attr }
  { a : Attr }
  { t : Term }
  { l : AttrList lst }
  : IsAttached a t l
  → a ∈ lst
  | @IsAttached.zeroth_attached lst' _ _ _ _ => List.Mem.head lst'
  | IsAttached.next_attached _ _ _ b _ _ _ isAttached' => List.Mem.tail b (isAttachedIsIn isAttached')

namespace Insert

  def insertAttachedStep
    { a b : Attr }
    { neq : a ≠ b }
    { t : Term }
    { lst : List Attr }
    { not_in : b ∉ lst }
    { u : OptionalAttr }
    { l : AttrList lst }
    (_ : IsAttached a t l)
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
    : IsAttached a t l
    → insert l a (attached t) = l
      | IsAttached.zeroth_attached _ _ _ _ => by simp [insert]
      | IsAttached.next_attached _ _ l b neq not_in u isAttached =>
          let step := @insertAttachedStep a b neq t _ not_in u _ isAttached
          Eq.trans step (congrArg (AttrList.cons b not_in u) (insertAttached isAttached))

  def insertTwice
    {lst : List Attr}
    (l : AttrList lst)
    (a : Attr)
    (t t' : Term)
    : insert (insert l a (attached t')) a (attached t) = insert l a (attached t)
    := match lst with
      | [] => match l with
        | AttrList.nil => by simp [insert]
      | b :: bs => match l with
        | AttrList.cons _ not_in _ tail => dite (a = b)
          (λ eq => by simp [insert, eq])
          (λ neq =>
            let neq' : b ≠ a := λ eq => neq eq.symm
            by  simp [insert, neq']
                exact insertTwice tail a t t'
          )

  def insert_new_isAttached
    { lst : List Attr }
    { l : AttrList lst }
    { a : Attr }
    { t t' : Term}
    : IsAttached a t l → IsAttached a t' (insert l a (attached t'))
    := λ isAttached => match isAttached with
      | IsAttached.zeroth_attached _ not_in _ _=> by
        simp [insert]
        exact IsAttached.zeroth_attached _ _ _ _
      | IsAttached.next_attached _ _ l b neq not_in u new_isAttached => by
        have hypothesis : IsAttached a t' (insert l a (attached t'))
          := insert_new_isAttached new_isAttached
        simp [insert, neq.symm]
        exact IsAttached.next_attached a t' (insert l a (attached t')) b neq not_in u hypothesis

end Insert

namespace Reduce

  inductive Reduce : Term → Term → Type where
    | congOBJ
      : { t : Term }
      → { t' : Term }
      → (b : Attr)
      → { lst : List Attr }
      → (l : AttrList lst)
      → Reduce t t'
      → IsAttached b t l
      → Reduce (obj l) (obj (insert l b (attached t')))
    | congDOT : ∀ t t' a, Reduce t t' → Reduce (dot t a) (dot t' a)
    | congAPPₗ : ∀ t t' u a, Reduce t t' → Reduce (app t a u) (app t' a u)
    | congAPPᵣ : ∀ t u u' a, Reduce u u' → Reduce (app t a u) (app t a u')
    | dot_c
      : { t : Term }
      → (t_c : Term)
      → (c : Attr)
      → { lst : List Attr }
      → (l : AttrList lst)
      → t = obj l
      → lookup l c = some (attached t_c)
      → Reduce (dot t c) (substitute (0, t) t_c)
    | dot_cφ
      : { t : Term }
      → (c : Attr)
      → { lst : List Attr }
      → (l : AttrList lst)
      → t = obj l
      → lookup l c = none
      → IsAttr "φ" t
      → Reduce (dot t c) (dot (dot t "φ") c)
    | app_c
      : (t u : Term)
      → (c : Attr)
      → { lst : List Attr }
      → (l : AttrList lst)
      → t = obj l
      → lookup l c = some void
      → Reduce (app t c u) (obj (insert l c (attached (incLocators u))))

open Reduce

namespace PReduce
  mutual
    -- | tᵢ => tᵢ' for all i with ⟦ ... αᵢ ↦ tᵢ ... ⟧
    --   α's are given by `lst`
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
        → PReduce (obj l) (obj newAttrs)
      | pcong_ρ : ∀ n, PReduce (loc n) (loc n)
      | pcongDOT : ∀ t t' a, PReduce t t' → PReduce (dot t a) (dot t' a)
      | pcongAPP : ∀ t t' u u' a, PReduce t t' → PReduce u u' → PReduce (app t a u) (app t' a u')
      | pdot_c
        : { t t' : Term }
        → (t_c : Term)
        → (c : Attr)
        → { lst : List Attr }
        → (l : AttrList lst)
        → PReduce t t'
        → t' = obj l
        → lookup l c = some (attached t_c)
        → PReduce (dot t c) (substitute (0, t') t_c)
      | pdot_cφ
        : { t t' : Term }
        → (c : Attr)
        → { lst : List Attr }
        → (l : AttrList lst)
        → PReduce t t'
        → t' = obj l
        → lookup l c = none
        → IsAttr "φ" t'
        → PReduce (dot t c) (dot (dot t' "φ") c)
      | papp_c
        : { t t' u u' : Term }
        → (c : Attr)
        → { lst : List Attr }
        → (l : AttrList lst)
        → PReduce t t'
        → PReduce u u'
        → t' = obj l
        → lookup l c = some void
        → PReduce (app t c u) (obj (insert l c (attached (incLocators u'))))
  end

-- [KS22, Proposition 3.3 (Reflexivity of parallel reduction)]
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
            PReduce.pcongOBJ _ _ premise
  end

  def singlePremise
    { lst : List Attr }
    : (l : AttrList lst)
    → (a : Attr)
    → (t : Term)
    → (t' : Term)
    → IsAttached a t l
    → PReduce t t'
    → Premise l (insert l a (attached t'))
    := λ l a t t' isAttached preduce => match lst with
      | [] => match l with
        | AttrList.nil => Premise.nil
      | b :: bs => match isAttached with
        | IsAttached.zeroth_attached _ _ _ tail => match l with
          | AttrList.cons _ _ _ _ => by
              simp [insert]
              exact Premise.consAttached b t t' preduce (reflexivePremise tail)
        | IsAttached.next_attached _ _ tail _ neq not_in u newIsAttached => match l with
          | AttrList.cons _ _ _ _ => by
              have neq' : b ≠ a := λ eq => neq eq.symm
              simp [insert, neq']
              have premise := (singlePremise tail a t t' newIsAttached preduce)
              exact (match u with
                | void => Premise.consVoid b premise
                | attached u' => Premise.consAttached b u' u' (prefl u') premise
              )
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
scoped infix:20 " ⇛* " => ParMany

-- [KS22, Proposition 3.4 (1), Eqivalence of ⇛ and ⇝]
def reg_to_par {t t' : Term} : (t ⇝ t') → (t ⇛ t')
  | .congOBJ b l red isAttached =>
      .pcongOBJ
        l
        (insert l b (attached _))
        (PReduce.singlePremise l b _ _ isAttached (reg_to_par red))
  | .congDOT t t' a red =>
      .pcongDOT t t' a (reg_to_par red)
  | .congAPPₗ t t' u a red =>
      .pcongAPP t t' u u a (reg_to_par red) (prefl u)
  | .congAPPᵣ t u u' a red =>
      .pcongAPP t t u u' a (prefl t) (reg_to_par red)
  | @Reduce.dot_c t t_c c _ l eq lookup_eq =>
      .pdot_c t_c c l (prefl t) eq lookup_eq
  | @Reduce.dot_cφ t c _ l eq lookup_c isAttr_φ =>
      .pdot_cφ c l (prefl t) eq lookup_c isAttr_φ
  | Reduce.app_c t u c l eq lookup_eq =>
      PReduce.papp_c c l (prefl t) (prefl u) eq lookup_eq

-- [KS22, Lemma A.3 (Transitivity of ⇝*)]
def red_trans { t t' t'' : Term } : (t ⇝* t') → (t' ⇝* t'') → (t ⇝* t'')
  | RedMany.nil, reds => reds
  | RedMany.cons lm mn_many, reds => RedMany.cons lm (red_trans mn_many reds)

def notEqByMem
  { lst : List Attr }
  { a b : Attr }
  (a_is_in : a ∈ lst)
  (b_not_in : b ∉ lst)
  : a ≠ b
  := λ eq =>
    let memEq : List.Mem a lst = List.Mem b lst :=
      congrArg (λ x => Membership.mem x lst) eq
    b_not_in (Eq.mp memEq a_is_in)

def mapRedManyObj
  { lst : List Attr}
  (a : Attr)
  { not_in_a : a ∉ lst }
  (u_a  : OptionalAttr)
  { l1 l2 : AttrList lst }
  : (obj l1 ⇝* obj l2)
  → (obj (AttrList.cons a not_in_a u_a l1) ⇝* obj (AttrList.cons a not_in_a u_a l2))
  := λ redmany => match redmany with
    | RedMany.nil => RedMany.nil
    | RedMany.cons (@congOBJ t t' c _ _ red_tt' isAttached) reds =>
      have one_step : (obj (AttrList.cons a not_in_a u_a l1) ⇝
        obj (AttrList.cons a not_in_a u_a (insert l1 c (attached t')))) := by
          have c_is_in := isAttachedIsIn isAttached
          have a_not_in := not_in_a
          have neq_c_a : c ≠ a := notEqByMem c_is_in a_not_in
          have intermediate := congOBJ c (AttrList.cons a not_in_a u_a l1) red_tt'
            (IsAttached.next_attached c _ _ _ neq_c_a _ _ isAttached)
          simp [insert, neq_c_a.symm] at intermediate
          assumption
      (RedMany.cons one_step (mapRedManyObj _ _ reds))

-- [KS22, Lemma A.4 (1), Congruence for ⇝* in OBJ]
def congOBJClos
  { t t' : Term }
  { b : Attr }
  { lst : List Attr }
  { l : AttrList lst }
  : (t ⇝* t')
  → IsAttached b t l
  → (obj l ⇝* obj (insert l b (attached t')))
  := λ red_tt' isAttached => match red_tt' with
    | RedMany.nil => Eq.ndrec (RedMany.nil) (congrArg obj (Eq.symm (Insert.insertAttached isAttached)))
    | @RedMany.cons t t_i t' red redMany =>
      have ind_hypothesis : obj (insert l b (attached t_i)) ⇝* obj (insert (insert l b (attached t_i)) b (attached t'))
        := (congOBJClos redMany (Insert.insert_new_isAttached isAttached))
      RedMany.cons
        (congOBJ b l red isAttached)
        (Eq.ndrec ind_hypothesis
        (congrArg obj (Insert.insertTwice l b t' t_i)))

-- [KS22, Lemma A.4 (2), Congruence for ⇝* in DOT]
def congDotClos
  { t t' : Term }
  { a : Attr }
  : (t ⇝* t') → ((dot t a) ⇝* (dot t' a))
  | RedMany.nil => RedMany.nil
  | @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congDOT l m a lm) (congDotClos mn_many)

-- [KS22, Lemma A.4 (3), Congruence for ⇝* in APPₗ]
def congAPPₗClos
  { t t' u : Term }
  { a : Attr }
  : (t ⇝* t') → ((app t a u) ⇝* (app t' a u))
  | RedMany.nil => RedMany.nil
  | @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congAPPₗ l m u a lm) (congAPPₗClos mn_many)

-- [KS22, Lemma A.4 (4), Congruence for ⇝* in APPᵣ]
def congAPPᵣClos
  { t u u' : Term }
  { a : Attr }
  : (u ⇝* u') → ((app t a u) ⇝* (app t a u'))
  | RedMany.nil => RedMany.nil
  | @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congAPPᵣ t l m a lm) (congAPPᵣClos mn_many)

-- [KS22, Proposition 3.4 (3), Eqivalence of ⇛ and ⇝]
def par_to_redMany {t t' : Term} : (t ⇛ t') → (t ⇝* t')
  | @PReduce.pcongOBJ lst l l' premise =>
    let rec fold_premise
      { lst : List Attr }
      { al al' : AttrList lst }
      (premise : Premise al al')
      : (obj al) ⇝* (obj al')
      := match lst with
        | [] => match al, al' with
          | AttrList.nil, AttrList.nil => RedMany.nil
        | a :: as => match al, al' with
          | AttrList.cons _ not_in u tail, AttrList.cons _ _ u' tail' => match premise with
            | Premise.consVoid _ premiseTail => mapRedManyObj a void (fold_premise premiseTail)
            | @Premise.consAttached _ t1 t2 preduce _ l1 l2 not_in premiseTail => by
                suffices temp : obj (insert (AttrList.cons a not_in (attached t1) l1) a (attached t2)) ⇝*
                  obj (AttrList.cons a _ (attached t2) l2) from
                  (red_trans
                    (congOBJClos (par_to_redMany preduce) (IsAttached.zeroth_attached a _ t1 l1))
                    (temp))
                simp [insert]
                exact mapRedManyObj a (attached t2) (fold_premise premiseTail)
    fold_premise premise
  | .pcong_ρ n => RedMany.nil
  | .pcongDOT t t' a prtt' => congDotClos (par_to_redMany prtt')
  | .pcongAPP t t' u u' a prtt' pruu' => red_trans
    (congAPPₗClos (par_to_redMany prtt'))
    (congAPPᵣClos (par_to_redMany pruu'))
  | PReduce.pdot_c t_c c l preduce eq lookup_eq =>
    let tc_t'c_many := congDotClos (par_to_redMany preduce)
    let tc_dispatch := Reduce.dot_c t_c c l eq lookup_eq
    let tc_dispatch_clos := RedMany.cons tc_dispatch RedMany.nil
    red_trans tc_t'c_many tc_dispatch_clos
  | PReduce.pdot_cφ c l preduce eq lookup_eq isAttr =>
    let tc_t'c_many := congDotClos (par_to_redMany preduce)
    let tφc_dispatch := dot_cφ c l eq lookup_eq isAttr
    let tφc_dispatch_clos := RedMany.cons tφc_dispatch RedMany.nil
    red_trans tc_t'c_many tφc_dispatch_clos
  | @PReduce.papp_c t t' u u' c lst l prtt' pruu' path_t'_obj_lst path_lst_c_void =>
    let tu_t'u_many := congAPPₗClos (par_to_redMany prtt')
    let t'u_t'u'_many := congAPPᵣClos (par_to_redMany pruu')
    let tu_t'u'_many := red_trans tu_t'u_many t'u_t'u'_many
    let tu_app := app_c t' u' c l path_t'_obj_lst path_lst_c_void
    let tu_app_clos := RedMany.cons tu_app RedMany.nil
    red_trans tu_t'u'_many tu_app_clos

-- [KS22, Proposition 3.4 (4), Eqivalence of ⇛ and ⇝]
def parMany_to_redMany {t t' : Term} : (t ⇛* t') → (t ⇝* t')
  | ParMany.nil => RedMany.nil
  | ParMany.cons red reds => red_trans (par_to_redMany red) (parMany_to_redMany reds)

-- [KS22, Proposition 3.4 (2), Eqivalence of ⇛ and ⇝]
def redMany_to_parMany {t t' : Term} : (t ⇝* t') → (t ⇛* t')
  | RedMany.nil => ParMany.nil
  | RedMany.cons red reds => ParMany.cons (reg_to_par red) (redMany_to_parMany reds)

-------------------------------------------------------
-- properties of mapAttrList
namespace MapAttrList
  def mapAttrList_compose
    (f g : Term → Term )
    { lst : List Attr }
    ( l : AttrList lst)
    : mapAttrList f (mapAttrList g l) = mapAttrList (λ t => f (g t)) l
    := match l with
      | AttrList.nil => rfl
      | AttrList.cons _ _ u tail => by
        cases u <;> simp [mapAttrList] <;> exact mapAttrList_compose f g tail

  def mapAttrList_lookup_attached
    ( f : Term → Term)
    { lst : List Attr}
    { l : AttrList lst}
    { t_c : Term}
    { c : Attr}
    : lookup l c = some (attached t_c) →
      lookup (mapAttrList f l) c = some (attached (f t_c))
    := λ lookup_eq => by match l with
      | AttrList.nil => contradiction
      | AttrList.cons name _ u tail =>
        simp [lookup] at *
        split
        . rename_i eq
          simp [eq] at lookup_eq
          simp [lookup_eq]
        . rename_i neq
          simp [neq] at lookup_eq
          exact mapAttrList_lookup_attached f lookup_eq

  def mapAttrList_lookup_void
    ( f : Term → Term)
    { lst : List Attr}
    { l : AttrList lst}
    { c : Attr}
    : lookup l c = some void → lookup (mapAttrList f l) c = some void
    := λ lookup_eq => by match l with
      | AttrList.nil => contradiction
      | AttrList.cons name _ u tail =>
        simp [lookup] at *
        split
        . rename_i eq
          simp [eq] at lookup_eq
          simp [lookup_eq]
        . rename_i neq
          simp [neq] at lookup_eq
          exact mapAttrList_lookup_void f lookup_eq

  def mapAttrList_lookup_none
    ( f : Term → Term)
    { lst : List Attr}
    { l : AttrList lst}
    { c : Attr}
    : lookup l c = none →
      lookup (mapAttrList f l) c = none
    := λ lookup_eq => by match l with
      | AttrList.nil => rfl
      | AttrList.cons name _ u tail =>
        simp [lookup] at *
        split
        . rename_i eq
          simp [eq] at lookup_eq
        . rename_i neq
          simp [neq] at lookup_eq
          exact mapAttrList_lookup_none f lookup_eq

  def mapAttrList_isAttr
    ( c : Attr)
    { lst : List Attr}
    ( l : AttrList lst)
    ( f : Term → Term)
    : IsAttr c (obj l) → IsAttr c (obj (mapAttrList f l))
    | @IsAttr.is_attr lst a _in _ => by
      exact @IsAttr.is_attr lst a _in (mapAttrList f l)
end MapAttrList

instance : Min (Option Nat) where
  min
  | some k1, some k2 => some (min k1 k2)
  | some k, none => some k
  | none, some k => some k
  | none, none => none

-- Definition. Minimal free locator in a term, if free locators exist, if we consider free locators start at `zeroth_level`.
def min_free_loc
  (zeroth_level : Nat)
  : Term → Option Nat
  | loc k => if k < zeroth_level then none
    else some (k - zeroth_level)
  | dot t _ => min_free_loc zeroth_level t
  | app t _ u => min (min_free_loc zeroth_level t) (min_free_loc zeroth_level u)
  | obj o => match o with
    | AttrList.nil => none
    | AttrList.cons _ _ void tail => min_free_loc zeroth_level (obj tail)
    | AttrList.cons _ _ (attached t) tail =>
      min
      (min_free_loc (zeroth_level + 1) t)
      (min_free_loc zeroth_level (obj tail))

def le_nat_option_nat : Nat → Option Nat → Prop
  | n, some k => n ≤ k
  | _, none   => True

def le_min_option
  { j : Nat}
  { option_n1 option_n2 : Option Nat}
  ( le_min : le_nat_option_nat j (min option_n1 option_n2))
  : le_nat_option_nat j option_n1 ∧ le_nat_option_nat j option_n2 := by
  match option_n1, option_n2 with
  | some n1, some n2 =>
    simp [le_nat_option_nat] at *
    simp [Nat.min_def] at le_min
    split at le_min
    . constructor
      . assumption
      . apply Nat.le_trans le_min (by assumption)
    . constructor
      . exact Nat.le_of_lt (Nat.lt_of_le_of_lt le_min (Nat.gt_of_not_le (by assumption)))
      . assumption
  | some n, none => simp [le_nat_option_nat] at * ; assumption
  | none, some n => simp [le_nat_option_nat] at * ; assumption
  | none, none   => simp [le_nat_option_nat] at *

def le_min_option_reverse
  { j : Nat}
  { option_n1 option_n2 : Option Nat}
  ( le_and : le_nat_option_nat j option_n1 ∧ le_nat_option_nat j option_n2)
  : le_nat_option_nat j (min option_n1 option_n2) := by
  match option_n1, option_n2 with
  | some n1, some n2 =>
    simp [le_nat_option_nat] at *
    simp [Nat.min_def]
    split
    . exact le_and.left
    . exact le_and.right
  | some n, none => simp [le_nat_option_nat] at * ; assumption
  | none, some n => simp [le_nat_option_nat] at * ; assumption
  | none, none   => simp [le_nat_option_nat] at *

-- IncLocatorsFrom increments minimal free locator if it acts only on free locators
def min_free_loc_inc
  { i j : Nat}
  { v : Term}
  ( free_locs_v : le_nat_option_nat i (min_free_loc j v))
  : le_nat_option_nat (i + 1) (min_free_loc j (incLocatorsFrom j v)) := by
  match v with
  | loc k =>
    simp [incLocatorsFrom]
    split
    . rename_i lt_kj
      simp [min_free_loc, lt_kj]
      simp [le_nat_option_nat]
    . rename_i nlt_kj
      simp [min_free_loc, nlt_kj, le_nat_option_nat] at free_locs_v
      simp [min_free_loc]
      have le_jk : j ≤ k := Nat.ge_of_not_lt nlt_kj
      have le_jk1 : j ≤ k+1 := Nat.le_succ_of_le le_jk
      have nlt_k1j : ¬ k + 1 < j := λ x => Nat.lt_irrefl j (Nat.lt_of_le_of_lt le_jk1 x)
      simp [le_nat_option_nat, nlt_k1j]
      have zzz : (i + j) + 1 ≤ k + 1 := Nat.succ_le_succ (Nat.add_le_of_le_sub le_jk free_locs_v)
      rw [Nat.add_right_comm] at zzz
      exact Nat.le_sub_of_add_le zzz
  | dot t _ =>
    simp [incLocatorsFrom]
    simp [min_free_loc] at *
    apply min_free_loc_inc free_locs_v
  | app t _ u =>
    simp [incLocatorsFrom, min_free_loc]
    apply le_min_option_reverse
    simp [min_free_loc] at free_locs_v
    have free_locs_v := le_min_option free_locs_v
    constructor <;> simp [min_free_loc] at *
    . exact min_free_loc_inc free_locs_v.left
    . exact min_free_loc_inc free_locs_v.right
  | obj o =>
    simp [incLocatorsFrom]
    let rec traverse_bindings
    { lst : List Attr}
    ( bindings : AttrList lst)
    ( free_locs : le_nat_option_nat i (min_free_loc j (obj bindings)))
    : le_nat_option_nat (i + 1) (min_free_loc j (obj (mapAttrList (incLocatorsFrom (j + 1)) bindings)))
    := by match bindings with
      | AttrList.nil =>
        simp [mapAttrList]
        simp [min_free_loc, le_nat_option_nat]
      | AttrList.cons _ _ void tail =>
        simp [mapAttrList, min_free_loc]
        exact traverse_bindings tail (by simp [min_free_loc] at free_locs ; exact free_locs)
      | AttrList.cons _ _ (attached term) tail =>
        simp [mapAttrList, min_free_loc]
        apply le_min_option_reverse
        constructor
        . simp [min_free_loc] at free_locs
          have free_locs := (le_min_option free_locs).left
          exact min_free_loc_inc free_locs
        . simp [min_free_loc] at free_locs
          have free_locs := le_min_option free_locs
          exact traverse_bindings tail free_locs.right
    exact traverse_bindings o free_locs_v

-- `substitute (j, _)` and `incLocatorsFrom k` cancel each other, if they act free locators
def subst_inc_cancel
  (v u : Term)
  (j k i zeroth_level : Nat)
  (le_ji : j ≤ i + zeroth_level)
  (le_ki : k ≤ i + zeroth_level)
  (le_0j : zeroth_level ≤ j)
  (le_0k : zeroth_level ≤ k)
  (v_loc : le_nat_option_nat i (min_free_loc zeroth_level v))
  : v = substitute (j, u) (incLocatorsFrom k v)
  := match v with
  | loc n => by
    simp [min_free_loc] at v_loc
    split at v_loc
    . rename_i n_is_not_free
      simp [incLocatorsFrom, Nat.lt_of_lt_of_le n_is_not_free le_0k]
      simp [substitute, Nat.lt_of_lt_of_le n_is_not_free le_0j]
    . rename_i n_is_free
      simp [le_nat_option_nat] at v_loc
      have n_is_free : zeroth_level ≤ n := Nat.ge_of_not_lt n_is_free
      have le_in: i + zeroth_level ≤ n :=
        (Nat.sub_add_cancel n_is_free) ▸ Nat.add_le_add_right v_loc zeroth_level
      have le_kn : k ≤ n := Nat.le_trans le_ki le_in
      have nlt_nk: ¬ n < k := λ x => Nat.lt_irrefl n (Nat.lt_of_lt_of_le x le_kn)
      simp [incLocatorsFrom, nlt_nk]
      have lt_jn1 : j < n + 1 := Nat.lt_succ_of_le (Nat.le_trans le_ji le_in)
      have nlt_n1j : ¬ n + 1 < j := λ x => Nat.lt_irrefl j (Nat.lt_trans lt_jn1 x)
      have neq_n1j : ¬ n + 1 = j := λ x => Nat.lt_irrefl j (x ▸ lt_jn1)
      simp [substitute, nlt_n1j, neq_n1j, Nat.add_sub_cancel]
  | dot t _ => by
    simp [incLocatorsFrom, substitute]
    apply subst_inc_cancel _ _ _ _ _ _ le_ji le_ki le_0j le_0k
      (by simp [min_free_loc] at v_loc ; exact v_loc)
  | app t _ u => by
    simp [min_free_loc] at v_loc
    have v_loc := le_min_option v_loc
    simp [incLocatorsFrom, substitute]
    constructor <;> apply subst_inc_cancel _ _ _ _ _ _ le_ji le_ki le_0j le_0k
    . exact v_loc.left
    . exact v_loc.right
  | obj o => by
    simp [incLocatorsFrom, substitute, MapAttrList.mapAttrList_compose]
    let rec traverse_bindings
    { lst : List Attr}
    ( bindings : AttrList lst)
    ( free_locs : le_nat_option_nat i (min_free_loc zeroth_level (obj bindings)))
    : bindings = mapAttrList (fun t => substitute (j + 1, incLocators u) (incLocatorsFrom (k + 1) t)) bindings
    := by match bindings with
      | AttrList.nil =>
        simp [mapAttrList]
      | AttrList.cons _ _ void tail =>
        simp [mapAttrList]
        exact traverse_bindings tail (by simp [min_free_loc] at free_locs ; assumption)
      | AttrList.cons _ _ (attached term) tail =>
        simp [mapAttrList]
        constructor
        . simp [min_free_loc] at free_locs
          have free_locs_term := (le_min_option free_locs).left
          exact subst_inc_cancel
            term
            _
            (j + 1)
            (k + 1)
            i
            (zeroth_level + 1)
            (by rw [← Nat.add_assoc] ; exact Nat.succ_le_succ le_ji)
            (by rw [← Nat.add_assoc] ; exact Nat.succ_le_succ le_ki)
            (Nat.succ_le_succ le_0j)
            (Nat.succ_le_succ le_0k)
            (free_locs_term)
        . simp [min_free_loc] at free_locs
          have free_locs := le_min_option free_locs
          exact traverse_bindings tail free_locs.right
    exact traverse_bindings o v_loc
decreasing_by sorry

-- [KS22, Lemma A.9, Increment swap]
def inc_swap
  ( i j : Nat)
  ( le_ij : i ≤ j)
  ( t : Term)
  : incLocatorsFrom i (incLocatorsFrom j t) = incLocatorsFrom (j + 1) (incLocatorsFrom i t)
  := match t with
    | loc k => by
      simp [incLocatorsFrom]
      split
      . rename_i lt_kj
        simp [incLocatorsFrom]
        split
        . rename_i lt_ki
          have lt_kj1 : k < j + 1 := Nat.lt_trans lt_kj (Nat.lt_succ_self j)
          simp [incLocatorsFrom, lt_kj1]
        . rename_i nlt_ki
          simp [incLocatorsFrom, Nat.succ_lt_succ lt_kj]
      . rename_i nlt_kj
        have le_ik : i ≤ k := Nat.le_trans le_ij (Nat.ge_of_not_lt nlt_kj)
        have nlt_k1i: ¬ k + 1 < i :=
          λ x => absurd ((Nat.lt_trans (Nat.lt_of_le_of_lt le_ik (Nat.lt_succ_self k)) x)) (Nat.lt_irrefl i)
        have nlt_ki : ¬ k < i := λ x => absurd le_ik (Nat.not_le_of_gt x)
        have nlt_k1j1 : ¬ k + 1 < j + 1 := λ x => nlt_kj (Nat.lt_of_succ_lt_succ x)
        simp [incLocatorsFrom, nlt_k1i, nlt_ki, nlt_k1j1]
    | dot s a => by
      simp [incLocatorsFrom]
      exact inc_swap i j le_ij s
    | app s a u => by
      simp [incLocatorsFrom]
      constructor
      . exact inc_swap i j le_ij s
      . exact inc_swap i j le_ij u
    | obj _ => by
      have ih : (t' : Term) → incLocatorsFrom (i + 1) (incLocatorsFrom (j + 1) t') = incLocatorsFrom (j + 1 + 1) (incLocatorsFrom (i + 1) t') :=
        λ t' => inc_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ij) t'
      simp [incLocatorsFrom, MapAttrList.mapAttrList_compose, ih]
decreasing_by sorry

-- [KS22, Lemma A.8, Increment and substitution swap]
def subst_inc_swap
  ( i j : Nat)
  ( le_ji : j ≤ i)
  ( t u : Term)
  : substitute (i+1, incLocatorsFrom j u) (incLocatorsFrom j t) =
    (incLocatorsFrom j (substitute (i, u) t))
  := match t with
    | loc k => by
      simp [substitute, incLocatorsFrom]
      split
      . rename_i lt_kj
        have lt_ki: k < i := Nat.lt_of_lt_of_le lt_kj le_ji
        have lt_ki1 : k < i + 1 := Nat.lt_succ_of_le (Nat.le_of_lt lt_ki)
        simp [substitute, lt_ki1, lt_ki, incLocatorsFrom, lt_kj]
      . rename_i nlt_kj
        split
        . rename_i lt_ki
          have lt_k1i1 : k + 1 < i + 1 := Nat.succ_lt_succ lt_ki
          simp [substitute, incLocatorsFrom, lt_k1i1, nlt_kj]
        . rename_i nlt_ki
          have nlt_k1i1 : ¬k + 1 < i + 1
            := λ x => absurd (Nat.lt_of_succ_lt_succ x) nlt_ki
          simp [substitute, nlt_k1i1]
          split
          . rename_i eq_ki
            rfl
          . rename_i neq_ki
            have neq_ik : ¬ i = k := λ eq => neq_ki eq.symm
            have lt_ik : i < k := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt nlt_ki) neq_ik
            have lt_jk : j < k := Nat.lt_of_le_of_lt le_ji lt_ik
            have le_k1 : 1 ≤ k := Nat.succ_le_of_lt
              (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
            have k0 : k - 1 + 1 = k := Nat.sub_add_cancel le_k1
            have lt_j1k1 : j + 1 < k + 1 := Nat.succ_lt_succ lt_jk
            have le_j1k : j + 1 ≤ k := Nat.le_of_lt_succ lt_j1k1
            have le_jk1 := Nat.le_of_succ_le_succ (k0.symm ▸ le_j1k)
            have nlt_jk1: ¬k - 1 < j := λ x => absurd le_jk1 (Nat.not_le_of_gt x)
            simp [incLocatorsFrom, nlt_jk1, k0, Nat.add_sub_cancel]
    | dot s a => by
      simp [substitute, incLocatorsFrom]
      exact subst_inc_swap i j le_ji s u
    | app s₁ a s₂ => by
      simp [substitute, incLocatorsFrom]
      constructor
      . exact subst_inc_swap i j le_ji s₁ u
      . exact subst_inc_swap i j le_ji s₂ u
    | obj o => by
      have ih := λ t' => subst_inc_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ji) t' (incLocators u)
      have ih_func : (fun t' => substitute (i + 1 + 1, incLocatorsFrom (j + 1) (incLocators u)) (incLocatorsFrom (j + 1) t')) = (fun t' => incLocatorsFrom (j + 1) (substitute (i + 1, (incLocators u)) t')) := funext ih
      simp [substitute, incLocatorsFrom, MapAttrList.mapAttrList_compose]
      simp [incLocators]
      simp [inc_swap]
      rw [← incLocators]
      simp [ih_func]
decreasing_by sorry

-- [Increment and substitution swap, dual to A.8]
def inc_subst_swap
  ( i j : Nat)
  ( le_ji : j ≤ i)
  ( t u : Term)
  : incLocatorsFrom i (substitute (j, u) t) =
    substitute (j, incLocatorsFrom i u) (incLocatorsFrom (i + 1) t)
  := match t with
    | loc k => by
      simp [substitute, incLocatorsFrom]
      split
      . rename_i lt_kj
        have lt_ki: k < i := Nat.lt_of_lt_of_le lt_kj le_ji
        have lt_ki1 : k < i + 1 := Nat.lt_succ_of_le (Nat.le_of_lt lt_ki)
        simp[substitute, incLocatorsFrom,  lt_ki1, lt_ki, lt_kj]
      . rename_i nlt_kj
        split
        . rename_i eq_kj
          simp [substitute, eq_kj, Nat.lt_succ_of_le le_ji]
        . rename_i neq_kj
          have lt_jk : j < k := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt nlt_kj) (λ x => neq_kj x.symm)
          have le_k1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
          have k0 : k - 1 + 1 = k := Nat.sub_add_cancel le_k1
          split
          . rename_i lt_ki1
            have lt_k1i : k - 1 < i := Nat.lt_of_succ_lt_succ (k0.symm ▸ lt_ki1)
            simp [substitute, incLocatorsFrom, nlt_kj, neq_kj, lt_k1i]
          . rename_i nlt_ki1
            have nlt_k1i : ¬ k - 1 < i := λ x => by
              have lt_ki1 := Nat.add_lt_add_right x 1
              simp [Nat.sub_add_cancel le_k1] at lt_ki1
              exact nlt_ki1 lt_ki1
            have lt_ik : i < k := Nat.lt_of_succ_le (Nat.ge_of_not_lt nlt_ki1)
            have lt_jk1 : j < k + 1 := Nat.lt_trans (Nat.lt_of_le_of_lt le_ji lt_ik) (Nat.lt_succ_self k)
            have nlt_k1j : ¬ k + 1 < j := λ x =>
              (Nat.lt_irrefl j) (Nat.lt_trans lt_jk1 x)
            have neq_k1j : ¬ k + 1 = j := λ x =>
              (Nat.lt_irrefl j) (x ▸ lt_jk1 )
            simp [substitute, incLocatorsFrom, nlt_k1i, neq_k1j, nlt_k1j, k0, Nat.add_sub_cancel]
    | dot s a => by
      simp [substitute, incLocatorsFrom]
      exact inc_subst_swap i j le_ji s u
    | app s₁ a s₂ => by
      simp [substitute, incLocatorsFrom]
      constructor
      . exact inc_subst_swap i j le_ji s₁ u
      . exact inc_subst_swap i j le_ji s₂ u
    | obj o => by
      have ih := λ t' => inc_subst_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ji) t' (incLocators u)
      have ih_func := funext ih
      simp [substitute, incLocatorsFrom, MapAttrList.mapAttrList_compose]
      simp [incLocators]
      simp [inc_swap]
      rw [← incLocators]
      simp [ih_func]
decreasing_by sorry

-- [KS22, Lemma A.7, Substitutions swap]
def subst_swap
  ( i j : Nat)
  ( le_ji : j ≤ i)
  ( t u v : Term)
  ( free_locs_v : le_nat_option_nat i (min_free_loc 0 v))
  : substitute (i, v) (substitute (j, u) t) =
    substitute (j, substitute (i, v) u) (substitute (i+1, incLocators v) t)
  := match t with
    | loc k => by
        simp [substitute]
        split
        . rename_i lt_kj
          have lt_ki : k < i := Nat.le_trans lt_kj le_ji
          have lt_ki1 : k < i + 1 := Nat.le_step lt_ki
          simp [substitute, lt_kj, lt_ki, lt_ki1]
          -- case k < j
        . rename_i not_lt
          have le_jk: j ≤ k := Nat.ge_of_not_lt not_lt
          split
          . rename_i eq_kj
            have le_ki : k ≤ i := eq_kj ▸ le_ji
            have lt_ji1 : j < i + 1 :=  Nat.lt_succ_of_le le_ji
            simp [substitute, eq_kj, lt_ji1]
            -- case k == j
          . rename_i neq_kj
            have neq_jk : ¬j = k := λ eq => neq_kj eq.symm
            have lt_jk : j < k := Nat.lt_of_le_of_ne le_jk neq_jk
            simp [substitute]
            have le_k1: 1 ≤ k := Nat.succ_le_of_lt
              (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
            split
            . rename_i le_k1i
              have lt_ki1: k < i + 1 := by
                have temp := Nat.add_lt_add_right le_k1i 1
                simp [Nat.sub_add_cancel le_k1] at temp
                exact temp
              have nlt_kj : ¬ k < j := λ lt_kj => Nat.lt_irrefl k (Nat.lt_trans lt_kj lt_jk)
              simp [substitute, lt_ki1, neq_kj, nlt_kj]
              -- case j < k ≤ i
            . rename_i nlt_k1i
              split
              . rename_i eq_k1i
                have eq_ki1 : k = i + 1 := by
                  have temp : k - 1 + 1 = i + 1 := congrArg Nat.succ eq_k1i
                  simp [Nat.sub_add_cancel le_k1] at temp
                  exact temp
                simp [substitute, eq_ki1]
                exact subst_inc_cancel
                  v _
                  j 0 i 0
                  le_ji
                  (Nat.zero_le i)
                  (Nat.zero_le j)
                  (Nat.zero_le 0)
                  free_locs_v
              . rename_i neq_k1i
                have lt_ik1: i < k - 1 := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt (nlt_k1i)) (λ x => neq_k1i x.symm)
                have lt_i1k : i + 1 < k := by
                  have := Nat.add_lt_add_right lt_ik1 1
                  simp [Nat.sub_add_cancel le_k1] at this
                  exact this
                have nle_ki1 : ¬ k < i + 1 := λ x => Nat.lt_irrefl k (Nat.lt_trans x lt_i1k)
                have neq_ki1 : ¬ k = i + 1 := λ x => Nat.lt_irrefl k (x ▸ lt_i1k)
                simp [substitute, nle_ki1, neq_ki1]
                have nlt_k1j : ¬ k - 1 < j := λ x => Nat.lt_irrefl j
                  (Nat.lt_trans (Nat.lt_of_le_of_lt le_ji lt_ik1) x)
                have neq : ¬ k - 1 = j := λ x => Nat.lt_irrefl j
                  (Nat.lt_of_le_of_lt le_ji (x ▸ lt_ik1))
                simp [nlt_k1j, neq]
    | dot s a => by
      simp [substitute]
      apply subst_swap _ _ le_ji _ _ _ free_locs_v
    | app s₁ a s₂ => by
      simp [substitute]
      constructor <;> apply subst_swap _ _ le_ji _ _ _ free_locs_v
    | obj o => by
      simp [substitute]
      simp [MapAttrList.mapAttrList_compose]
      let rec traverse_bindings
      { lst : List Attr}
      ( bindings : AttrList lst)
      : mapAttrList (fun t => substitute (i + 1, incLocators v) (substitute (j + 1, incLocators u) t)) bindings = mapAttrList (fun t =>
      substitute (j + 1, incLocators (substitute (i, v) u)) (substitute (i + 1 + 1, incLocators (incLocators v)) t)) bindings
      := by match bindings with
        | AttrList.nil =>
          simp [mapAttrList]
        | AttrList.cons _ _ u tail =>
          simp [mapAttrList]
          split
          . constructor
            . rfl
            . exact traverse_bindings tail
          . constructor
            . rename_i term
              simp
              have ih := subst_swap
                (i+1)
                (j+1)
                (Nat.add_le_add_right le_ji 1)
                term (incLocators u) (incLocators v)
                (min_free_loc_inc free_locs_v)
              rw [incLocators] at ih
              simp [subst_inc_swap] at ih
              rw [← incLocators] at ih
              exact ih
            . exact traverse_bindings tail
      exact traverse_bindings o
decreasing_by sorry

namespace MapAttrList
  def mapAttrList_subst_insert
    { i : Nat }
    { c : Attr }
    { lst : List Attr }
    { l : AttrList lst }
    { u v : Term}
    : (insert (mapAttrList (substitute (i + 1, incLocators u)) l) c (attached (incLocators (substitute (i, u) v)))) =
    (mapAttrList (substitute (i + 1, incLocators u)) (insert l c (attached (incLocators v))))
    := match l with
    | AttrList.nil => by
      simp [insert, mapAttrList]
    | AttrList.cons a not_in op_attr tail => by
      simp [insert]
      split
      . rw [incLocators]
        simp [← subst_inc_swap]
        rw [mapAttrList]
      . split <;> simp [mapAttrList] <;> exact mapAttrList_subst_insert

  def mapAttrList_inc_insert
    { i : Nat }
    { c : Attr }
    { lst : List Attr }
    { l : AttrList lst }
    { v : Term}
    : (insert (mapAttrList (incLocatorsFrom (i + 1)) l) c (attached (incLocators (incLocatorsFrom i v)))) =
    (mapAttrList (incLocatorsFrom (i + 1)) (insert l c (attached (incLocators v))))
    := match l with
    | AttrList.nil => by
      simp [insert, mapAttrList]
    | AttrList.cons a not_in op_attr tail => by
      simp [insert]
      split
      . rw [incLocators]
        simp [inc_swap]
        simp [mapAttrList]
      . split <;> simp [mapAttrList] <;> exact mapAttrList_inc_insert
end MapAttrList

-- incLocators preserves parallel reduction
def preduce_incLocatorsFrom
  { t t' : Term}
  ( i : Nat)
  : ( t ⇛ t') → (incLocatorsFrom i t ⇛ incLocatorsFrom i t')
  | pcongOBJ bnds bnds' premise => by
    simp [incLocatorsFrom]
    let rec make_premise
      { lst : List Attr }
      { bnds bnds' : AttrList lst }
      (premise : Premise bnds bnds')
      : Premise (mapAttrList (incLocatorsFrom (i + 1)) bnds) (mapAttrList (incLocatorsFrom (i + 1)) bnds')
      := match lst with
        | [] => match bnds, bnds' with
          | AttrList.nil, AttrList.nil => by
            simp [mapAttrList]
            exact Premise.nil
        | a :: as => match premise with
          | Premise.consVoid a tail => by
            simp [mapAttrList]
            exact Premise.consVoid a (make_premise tail)
          | Premise.consAttached a t1 t2 preduce tail => by
            simp [mapAttrList]
            exact Premise.consAttached
              a
              _
              _
              (preduce_incLocatorsFrom (i+1) preduce)
              (make_premise tail)
    exact pcongOBJ _ _ (make_premise premise)
  | pcong_ρ n =>  prefl (incLocatorsFrom i (loc n))
  | pcongAPP t t' u u' a tt' uu' => by
    simp [incLocatorsFrom]
    apply pcongAPP
    . exact preduce_incLocatorsFrom i tt'
    . exact preduce_incLocatorsFrom i uu'
  | pcongDOT t t' a tt' => by
    simp [incLocatorsFrom]
    apply pcongDOT
    exact preduce_incLocatorsFrom i tt'
  | @pdot_c s s' t_c c lst l ss' eq lookup_eq => by
    simp [incLocatorsFrom]
    have := @pdot_c
      (incLocatorsFrom i s)
      (incLocatorsFrom i s')
      _
      c
      lst
      (mapAttrList (incLocatorsFrom (i+1)) l)
      (preduce_incLocatorsFrom i ss')
      (by simp [eq, incLocatorsFrom])
      (MapAttrList.mapAttrList_lookup_attached (incLocatorsFrom (i + 1)) lookup_eq)
    simp [inc_subst_swap]
    assumption
  | @pdot_cφ s s' c lst l ss' eq lookup_eq is_attr => by
    simp [incLocatorsFrom]
    rw [eq] at is_attr
    have is_attr' : IsAttr "φ" (incLocatorsFrom i (obj l)) := by
      simp [incLocatorsFrom]
      exact MapAttrList.mapAttrList_isAttr "φ" l (incLocatorsFrom (i + 1)) is_attr
    rw [← eq] at is_attr'
    exact @pdot_cφ
        (incLocatorsFrom i s)
        (incLocatorsFrom i s')
        c
        lst
        (mapAttrList (incLocatorsFrom (i + 1)) l)
        (preduce_incLocatorsFrom i ss')
        (by rw [eq, incLocatorsFrom])
        (MapAttrList.mapAttrList_lookup_none (incLocatorsFrom (i + 1)) lookup_eq)
        (is_attr')
  | @papp_c s s' v v' c lst l ss' vv' eq lookup_eq => by
    simp [incLocatorsFrom]
    have := @papp_c
      (incLocatorsFrom i s)
      (incLocatorsFrom i s')
      (incLocatorsFrom i v)
      (incLocatorsFrom i v')
      c
      lst
      (mapAttrList (incLocatorsFrom (i + 1)) l)
      (preduce_incLocatorsFrom i ss')
      (preduce_incLocatorsFrom i vv')
      (by rw [eq, incLocatorsFrom])
      (MapAttrList.mapAttrList_lookup_void (incLocatorsFrom (i + 1)) lookup_eq)
    simp [MapAttrList.mapAttrList_inc_insert] at this
    exact this

def get_premise
  { attrs : List Attr }
  { bnds bnds' : AttrList attrs }
  (preduce : obj bnds ⇛ obj bnds')
  : Premise bnds bnds'
  := match preduce with
    | PReduce.pcongOBJ _ _ premise => premise

-- [KS22, Lemma 3.5]
def substitution_lemma
  ( i : Nat )
  { t t' u u' : Term }
  (tt' : t ⇛ t')
  (uu' : u ⇛ u')
  (min_free_locs_u' : le_nat_option_nat i (min_free_loc 0 u'))
  : substitute (i, u) t ⇛ substitute (i, u') t'
  := match tt' with
    | @pcongOBJ attrs bnds bnds' premise =>
      let rec fold_premise
      { lst : List Attr }
      { al al' : AttrList lst }
      (premise : Premise al al')
      : substitute (i, u) (obj al) ⇛ substitute (i, u') (obj al')
      := match lst with
        | [] => match al, al' with
          | AttrList.nil, AttrList.nil => by
            simp [substitute, mapAttrList]
            exact prefl (obj AttrList.nil)
        | a :: as => match al, al' with
          | AttrList.cons _ not_in op_attr tail, AttrList.cons _ _ op_attr' tail' => match premise with
            | Premise.consVoid _ premiseTail => by
              simp [substitute, mapAttrList]
              let h := fold_premise premiseTail
              simp [substitute] at h
              have subst_premise := get_premise h
              exact PReduce.pcongOBJ _ _ (Premise.consVoid a subst_premise)
            | @Premise.consAttached _ t1 t2 preduce_t1_t2 _ l1 l2 not_in premiseTail => by
              simp [substitute, mapAttrList]
              have h1 := substitution_lemma (i + 1) preduce_t1_t2 (preduce_incLocatorsFrom 0 uu') (by rw [← incLocators] ; exact min_free_loc_inc min_free_locs_u')
              have h2 := fold_premise premiseTail
              simp [substitute] at h2
              have subst_premise := get_premise h2
              have premise := @Premise.consAttached
                a
                (substitute (i + 1, incLocators u) t1)
                (substitute (i + 1, incLocators u') t2)
                h1
                as
                (mapAttrList (substitute (i + 1, incLocators u)) l1)
                (mapAttrList (substitute (i + 1, incLocators u')) l2)
                not_in
                subst_premise
              exact PReduce.pcongOBJ _ _ premise
      fold_premise premise
    | pcong_ρ n => by
        simp [substitute]
        exact dite (n < i)
          (λ less => by
            simp [less]
            exact pcong_ρ n
          )
          (λ not_less =>
            dite (n = i)
              (λ eq => by
                have obvious : ¬ i < i := Nat.lt_irrefl i
                simp [not_less, eq, obvious]
                exact uu'
              )
              (λ not_eq => by
                simp [not_less, not_eq]
                exact pcong_ρ (n - 1)
              )
          )
    | pcongDOT lt lt' a preduce => by
        simp [substitute]
        exact pcongDOT
          (substitute (i, u) lt)
          (substitute (i, u') lt')
          a
          (substitution_lemma i preduce uu' (by assumption))
    | pcongAPP lt lt' lu lu' a preduce_t preduce_u => by
        simp [substitute]
        exact pcongAPP
          (substitute (i, u) lt)
          (substitute (i, u') lt')
          (substitute (i, u) lu)
          (substitute (i, u') lu')
          a
          (substitution_lemma i preduce_t uu' (by assumption))
          (substitution_lemma i preduce_u uu' (by assumption))
    | @pdot_c s s' t_c c lst l ss' eq lookup_eq => by
      have ih := substitution_lemma i ss' uu'
      have dot_subst : dot (substitute (i, u) s) c ⇛
        substitute (0, substitute (i, u') s') (substitute (i+1, incLocators u') t_c)
        := @PReduce.pdot_c
          (substitute (i, u) s)
          (substitute (i, u') s')
          (substitute (i+1, incLocators u') t_c)
          c
          lst
          (mapAttrList (substitute (i+1, incLocators u')) l)
          (substitution_lemma i ss' uu' (by assumption))
          (by rw [eq, substitute])
          (MapAttrList.mapAttrList_lookup_attached (substitute (i + 1, incLocators u')) lookup_eq)
      have : substitute (0, substitute (i, u') s') (substitute (i + 1, incLocators u') t_c) = substitute (i, u') (substitute (0, s') t_c) := (subst_swap i 0 (Nat.zero_le i) t_c s' u' ((by assumption))).symm
      simp [this] at dot_subst
      simp [substitute]
      exact dot_subst
    | @pdot_cφ s s' c lst l ss' eq lookup_eq is_attr => by
      rw [eq] at is_attr
      have is_attr' : IsAttr "φ" (substitute (i, u') (obj l)) := by
        simp [substitute]
        exact MapAttrList.mapAttrList_isAttr "φ" l (substitute (i + 1, incLocators u')) is_attr
      rw [← eq] at is_attr'
      simp [substitute]
      exact @pdot_cφ
        (substitute (i, u) s)
        (substitute (i, u') s')
        c
        lst
        (mapAttrList (substitute (i+1, incLocators u')) l)
        (substitution_lemma i ss' uu' (by assumption))
        (by rw [eq, substitute])
        (MapAttrList.mapAttrList_lookup_none (substitute (i + 1, incLocators u')) lookup_eq)
        (is_attr')
    | @papp_c s s' v v' c lst l ss' vv' eq lookup_eq => by
      simp [substitute]
      rw [← MapAttrList.mapAttrList_subst_insert]
      exact @papp_c
        (substitute (i, u) s)
        (substitute (i, u') s')
        (substitute (i, u) v)
        (substitute (i, u') v')
        c
        lst
        (mapAttrList (substitute (i+1, incLocators u')) l)
        (substitution_lemma i ss' uu' (by assumption))
        (substitution_lemma i vv' uu' ((by assumption)))
        (by rw [eq, substitute])
        (MapAttrList.mapAttrList_lookup_void (substitute (i + 1, incLocators u')) lookup_eq)
decreasing_by sorry


----------------------------------------------
-- Complete Development

def complete_development : Term → Term
  | loc n => loc n
  | dot t a => match (complete_development t) with
    | @obj attrs bnds => match (lookup bnds a) with
      | some (attached t_a) => (substitute (0, (obj bnds)) t_a)
      | some void => dot (obj bnds) a
      | none => if ("φ" ∈ attrs) then dot (dot (obj bnds) "φ") a else dot (obj bnds) a
    | t' => dot t' a
  | app t a u => match (complete_development t) with
    | @obj attrs bnds => match (lookup bnds a) with
      | some void => obj (insert bnds a (attached (incLocators u)))
      | _ => app (obj bnds) a (complete_development u)
    | _ => app (complete_development t) a (complete_development u)
  | obj bnds => obj (mapAttrList complete_development bnds)
decreasing_by sorry

def term_to_development
  (t : Term)
  : t ⇛ complete_development t
  := match t with
    | loc n => by simp [complete_development]; exact prefl (loc n)
    | dot t a => by
        simp [complete_development]
        split
        . rename_i cd_is_obj
          rename_i l
          rename_i attrs
          split
          . rename_i lookup_attached
            rename_i u
            have goal := PReduce.pdot_c u a l (term_to_development t) cd_is_obj lookup_attached
            simp [cd_is_obj] at goal
            exact goal
          . have goal := PReduce.pcongDOT t (complete_development t) a (term_to_development t)
            simp [cd_is_obj] at goal
            exact goal
          . rename_i lookup_none
            exact dite ("φ" ∈ attrs)
              (λ φ_in => by
                simp [φ_in]
                have temp := term_to_development t
                simp [cd_is_obj] at temp
                exact PReduce.pdot_cφ a l temp rfl lookup_none (IsAttr.is_attr "φ" φ_in l)
              )
              (λ not_in => by
                simp [not_in]
                have goal := PReduce.pcongDOT t (complete_development t) a (term_to_development t)
                simp [cd_is_obj] at goal
                exact goal
              )
        . rename_i cd_not_obj
          exact PReduce.pcongDOT t (complete_development t) a (term_to_development t)
    | app t a u => by
        simp [complete_development]
        split
        . rename_i cd_is_obj
          rename_i l
          split
          . rename_i lookup_void
            exact PReduce.papp_c a l (term_to_development t) (prefl u) cd_is_obj lookup_void
          . rename_i lookup_not_void
            have goal := PReduce.pcongAPP
              t
              (complete_development t)
              u
              (complete_development u)
              a
              (term_to_development t)
              (term_to_development u)
            simp [cd_is_obj] at goal
            exact goal
        . exact PReduce.pcongAPP
            t
            (complete_development t)
            u
            (complete_development u)
            a
            (term_to_development t)
            (term_to_development u)

    | obj bnds => by
        simp [complete_development]
        let rec make_premise
          { attrs : List Attr }
          (bnds : AttrList attrs)
          : Premise bnds (mapAttrList complete_development bnds)
          := match bnds with
            | AttrList.nil => Premise.nil
            | AttrList.cons a not_in void tail => by
                simp [mapAttrList]
                exact Premise.consVoid a (make_premise tail)
            | AttrList.cons a not_in (attached u) tail => by
                simp [mapAttrList]
                exact Premise.consAttached
                  a
                  u
                  (complete_development u)
                  (term_to_development u)
                  (make_premise tail)
        exact PReduce.pcongOBJ
          bnds
          (mapAttrList complete_development bnds)
          (make_premise bnds)
