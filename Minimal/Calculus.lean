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

def congDotClos
  { t t' : Term }
  { a : Attr }
  : (t ⇝* t') → ((dot t a) ⇝* (dot t' a))
  | RedMany.nil => RedMany.nil
  | @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congDOT l m a lm) (congDotClos mn_many)

def congAPPₗClos
  { t t' u : Term }
  { a : Attr }
  : (t ⇝* t') → ((app t a u) ⇝* (app t' a u))
  | RedMany.nil => RedMany.nil
  | @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congAPPₗ l m u a lm) (congAPPₗClos mn_many)

def congAPPᵣClos
  { t u u' : Term }
  { a : Attr }
  : (u ⇝* u') → ((app t a u) ⇝* (app t a u'))
  | RedMany.nil => RedMany.nil
  | @RedMany.cons l m n lm mn_many =>
    RedMany.cons (congAPPᵣ t l m a lm) (congAPPᵣClos mn_many)

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

def parMany_to_redMany {t t' : Term} : (t ⇛* t') → (t ⇝* t')
  | ParMany.nil => RedMany.nil
  | ParMany.cons red reds => red_trans (par_to_redMany red) (parMany_to_redMany reds)

def redMany_to_parMany {t t' : Term} : (t ⇝* t') → (t ⇛* t')
  | RedMany.nil => ParMany.nil
  | RedMany.cons red reds => ParMany.cons (reg_to_par red) (redMany_to_parMany reds)

-------------------------------------------------------

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

-- A.9 (Increment swap)
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
      simp [incLocatorsFrom, mapAttrList_compose, ih]
decreasing_by sorry

-- A.8 (Increment and substitution swap)
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
      simp [substitute, incLocatorsFrom, mapAttrList_compose]
      simp [incLocators]
      simp [inc_swap]
      rw [← incLocators]
      simp [ih_func]
decreasing_by sorry

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
      simp [substitute, incLocatorsFrom, mapAttrList_compose]
      simp [incLocators]
      simp [inc_swap]
      rw [← incLocators]
      simp [ih_func]
decreasing_by sorry

-- A.7 (Substitution swap)
def subst_swap
  ( i j : Nat)
  ( le_ji : j ≤ i)
  ( t u v : Term)
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
                admit
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
      apply subst_swap _ _ le_ji
    | app s₁ a s₂ => by
      simp [substitute]
      constructor <;> apply subst_swap _ _ le_ji
    | obj o => by
      simp [substitute]
      simp [mapAttrList_compose]
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
              have ih := subst_swap (i+1) (j+1) (Nat.add_le_add_right le_ji 1) term (incLocators u) (incLocators v)
              rw [incLocators] at ih
              simp [subst_inc_swap] at ih
              rw [← incLocators] at ih
              exact congrArg attached ih
            . exact traverse_bindings tail
      exact traverse_bindings o
      decreasing_by sorry

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
      (mapAttrList_lookup_attached (incLocatorsFrom (i + 1)) lookup_eq)
    simp [inc_subst_swap]
    assumption
  | @pdot_cφ s s' c lst l ss' eq lookup_eq is_attr => by
    simp [incLocatorsFrom]
    rw [eq] at is_attr
    have is_attr' : IsAttr "φ" (incLocatorsFrom i (obj l)) := by
      simp [incLocatorsFrom]
      exact mapAttrList_isAttr "φ" l (incLocatorsFrom (i + 1)) is_attr
    rw [← eq] at is_attr'
    exact @pdot_cφ
        (incLocatorsFrom i s)
        (incLocatorsFrom i s')
        c
        lst
        (mapAttrList (incLocatorsFrom (i + 1)) l)
        (preduce_incLocatorsFrom i ss')
        (by rw [eq, incLocatorsFrom])
        (mapAttrList_lookup_none (incLocatorsFrom (i + 1)) lookup_eq)
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
      (mapAttrList_lookup_void (incLocatorsFrom (i + 1)) lookup_eq)
    simp [mapAttrList_inc_insert] at this
    exact this

def substitution_lemma
  ( i : Nat )
  { t t' u u' : Term }
  (tt' : t ⇛ t')
  (uu' : u ⇛ u')
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
              have h := fold_premise premiseTail
              simp [substitute] at h
              match h with
                | PReduce.pcongOBJ _ _ subst_premise =>
                  exact PReduce.pcongOBJ _ _ (Premise.consVoid a subst_premise)
            | @Premise.consAttached _ t1 t2 preduce_t1_t2 _ l1 l2 not_in premiseTail => by
              simp [substitute, mapAttrList]
              have h1 := substitution_lemma (i + 1) preduce_t1_t2 (preduce_incLocatorsFrom 0 uu')
              have h2 := fold_premise premiseTail
              simp [substitute] at h2
              match h2 with
                | PReduce.pcongOBJ _ _ subst_premise =>
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
          (substitution_lemma i preduce uu')
    | pcongAPP lt lt' lu lu' a preduce_t preduce_u => by
        simp [substitute]
        exact pcongAPP
          (substitute (i, u) lt)
          (substitute (i, u') lt')
          (substitute (i, u) lu)
          (substitute (i, u') lu')
          a
          (substitution_lemma i preduce_t uu')
          (substitution_lemma i preduce_u uu')
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
          (substitution_lemma i ss' uu')
          (by rw [eq, substitute])
          (mapAttrList_lookup_attached (substitute (i + 1, incLocators u')) lookup_eq)
      simp [← subst_swap] at dot_subst
      simp [substitute]
      exact dot_subst
    | @pdot_cφ s s' c lst l ss' eq lookup_eq is_attr => by
      rw [eq] at is_attr
      have is_attr' : IsAttr "φ" (substitute (i, u') (obj l)) := by
        simp [substitute]
        exact mapAttrList_isAttr "φ" l (substitute (i + 1, incLocators u')) is_attr
      rw [← eq] at is_attr'
      simp [substitute]
      exact @pdot_cφ
        (substitute (i, u) s)
        (substitute (i, u') s')
        c
        lst
        (mapAttrList (substitute (i+1, incLocators u')) l)
        (substitution_lemma i ss' uu')
        (by rw [eq, substitute])
        (mapAttrList_lookup_none (substitute (i + 1, incLocators u')) lookup_eq)
        (is_attr')
    | @papp_c s s' v v' c lst l ss' vv' eq lookup_eq => by
      simp [substitute]
      rw [← mapAttrList_subst_insert]
      exact @papp_c
        (substitute (i, u) s)
        (substitute (i, u') s')
        (substitute (i, u) v)
        (substitute (i, u') v')
        c
        lst
        (mapAttrList (substitute (i+1, incLocators u')) l)
        (substitution_lemma i ss' uu')
        (substitution_lemma i vv' uu')
        (by rw [eq, substitute])
        (mapAttrList_lookup_void (substitute (i + 1, incLocators u')) lookup_eq)
decreasing_by sorry
