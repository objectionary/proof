import Minimal.ARS

/-!
# Confluence of minimal φ-calculus

This file contains a formalization of minimal φ-calculus and the proof of its confluence.

## References

* [Nikolai Kudasov and Violetta Sim. 2023. Formalizing 𝜑-Calculus: A Purely Object-Oriented Calculus of Decorated Objects.][KS22]
* [Jean L. Krivine. 1993. Lambda-Calculus, Types and Models. Ellis Horwood, USA.][Krivine93]
-/

set_option autoImplicit false
set_option linter.all true
set_option linter.missingDocs false

/-! ### Defition of minimal φ-calculus -/

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
    | loc : Nat → Term
    | dot : Term → Attr → Term
    | app : Term → Attr → Term → Term
    | obj : { lst : List Attr } → Bindings lst → Term
end
open OptionalAttr
open Term

/-! ### Defition of increment, substitution, its properties,
  and auxiliary definitions that involve terms
-/

mutual
  /-- Locator increment [KS22, Definition 2.5] -/
  @[simp]
  def incLocatorsFrom (n : Nat) (term : Term) : Term
    := match term with
      | loc m => if m < n then loc m else loc (m + 1)
      | dot t a => dot (incLocatorsFrom n t) a
      | app t a u => app (incLocatorsFrom n t) a (incLocatorsFrom n u)
      | obj o => (obj (incLocatorsFromLst (n + 1) o))

  @[simp]
  def incLocatorsFromLst
    ( n : Nat)
    { lst : List Attr}
    ( o : Bindings lst)
    : Bindings lst
    := match o with
    | Bindings.nil => Bindings.nil
    | Bindings.cons a not_in void tail =>
      Bindings.cons a not_in void (incLocatorsFromLst n tail)
    | Bindings.cons a not_in (attached term) tail =>
      Bindings.cons a not_in (attached (incLocatorsFrom n term)) (incLocatorsFromLst n tail)
end

def incLocators : Term → Term
  := incLocatorsFrom 0

mutual
/-- Locator substitution [KS22, Fig. 1] -/
  @[simp]
  def substitute : Nat × Term → Term → Term
  := fun (k, v) term => match term with
    | loc n =>
      if (n < k) then (loc n)
      else if (n == k) then v
      else loc (n-1)
    | dot t a => dot (substitute (k, v) t) a
    | app t a u => app (substitute (k, v) t) a (substitute (k, v) u)
    | obj o => obj (substituteLst (k + 1, incLocators v) o)

  @[simp]
  def substituteLst {lst : List Attr}
  : Nat × Term → Bindings lst → Bindings lst
  := fun (k, v) o => match o with
  | Bindings.nil => Bindings.nil
  | Bindings.cons a not_in void tail =>
    Bindings.cons a not_in void (substituteLst (k, v) tail)
  | Bindings.cons a not_in (attached term) tail =>
    Bindings.cons a not_in (attached (substitute (k, v) term)) (substituteLst (k, v) tail)
end

instance : Min (Option Nat) where
  min
  | some k1, some k2 => some (min k1 k2)
  | some k, none => some k
  | none, some k => some k
  | none, none => none

/-- Minimal free locator in a term, if free locators exist,
assuming free locators start at `zeroth_level`. -/
def min_free_loc
  (zeroth_level : Nat)
  : Term → Option Nat
  | loc k => if k < zeroth_level then none
    else some (k - zeroth_level)
  | dot t _ => min_free_loc zeroth_level t
  | app t _ u => min (min_free_loc zeroth_level t) (min_free_loc zeroth_level u)
  | obj o => match o with
    | Bindings.nil => none
    | Bindings.cons _ _ void tail => min_free_loc zeroth_level (obj tail)
    | Bindings.cons _ _ (attached t) tail =>
      min
      (min_free_loc (zeroth_level + 1) t)
      (min_free_loc zeroth_level (obj tail))

def le_nat_option_nat : Nat → Option Nat → Prop
  | n, some k => n ≤ k
  | _, none   => True

theorem le_min_option
  { j : Nat}
  { option_n1 option_n2 : Option Nat}
  ( le_min : le_nat_option_nat j (min option_n1 option_n2))
  : le_nat_option_nat j option_n1 ∧ le_nat_option_nat j option_n2 := by
  match option_n1, option_n2 with
  | some n1, some n2 =>
    simp [le_nat_option_nat] at *
    simp [Nat.min_def] at le_min
    split at le_min
    · constructor
      · assumption
      · apply Nat.le_trans le_min (by assumption)
    · constructor
      · exact Nat.le_of_lt (Nat.lt_of_le_of_lt le_min (Nat.gt_of_not_le (by assumption)))
      · assumption
  | some n, none => simp [le_nat_option_nat] at * ; assumption
  | none, some n => simp [le_nat_option_nat] at * ; assumption
  | none, none   => simp [le_nat_option_nat] at *

theorem le_min_option_reverse
  { j : Nat}
  { option_n1 option_n2 : Option Nat}
  ( le_and : le_nat_option_nat j option_n1 ∧ le_nat_option_nat j option_n2)
  : le_nat_option_nat j (min option_n1 option_n2) := by
  match option_n1, option_n2 with
  | some n1, some n2 =>
    simp [le_nat_option_nat] at *
    simp [Nat.min_def]
    split
    · exact le_and.left
    · exact le_and.right
  | some n, none => simp [le_nat_option_nat] at * ; assumption
  | none, some n => simp [le_nat_option_nat] at * ; assumption
  | none, none   => simp [le_nat_option_nat] at *

/-- `IncLocatorsFrom` increments minimal free locator if it acts only on free locators. -/
theorem min_free_loc_inc
  { i j : Nat}
  { v : Term}
  ( free_locs_v : le_nat_option_nat i (min_free_loc j v))
  : le_nat_option_nat (i + 1) (min_free_loc j (incLocatorsFrom j v)) := by
  match v with
  | loc k =>
    simp [incLocatorsFrom]
    split
    · rename_i lt_kj
      simp [min_free_loc, lt_kj]
      simp [le_nat_option_nat]
    · rename_i nlt_kj
      simp [min_free_loc, nlt_kj, le_nat_option_nat] at free_locs_v
      simp [min_free_loc]
      have le_jk : j ≤ k := Nat.ge_of_not_lt nlt_kj
      have le_jk1 : j ≤ k+1 := Nat.le_succ_of_le le_jk
      have nlt_k1j : ¬ k + 1 < j := fun x => Nat.lt_irrefl j (Nat.lt_of_le_of_lt le_jk1 x)
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
    · exact min_free_loc_inc free_locs_v.left
    · exact min_free_loc_inc free_locs_v.right
  | obj o =>
    simp [incLocatorsFrom]
    let rec traverse_bindings
    { lst : List Attr}
    ( bindings : Bindings lst)
    ( free_locs : le_nat_option_nat i (min_free_loc j (obj bindings)))
    : le_nat_option_nat (i + 1) (min_free_loc j (obj (incLocatorsFromLst (j + 1) bindings)))
    := by match bindings with
      | Bindings.nil =>
        simp [min_free_loc, le_nat_option_nat]
      | Bindings.cons _ _ void tail =>
        simp [min_free_loc]
        exact traverse_bindings tail (by simp [min_free_loc] at free_locs ; exact free_locs)
      | Bindings.cons _ _ (attached term) tail =>
        simp [min_free_loc]
        apply le_min_option_reverse
        constructor
        · simp [min_free_loc] at free_locs
          have free_locs := (le_min_option free_locs).left
          exact min_free_loc_inc free_locs
        · simp [min_free_loc] at free_locs
          have free_locs := le_min_option free_locs
          exact traverse_bindings tail free_locs.right
    exact traverse_bindings o free_locs_v


mutual
/-- `substitute` and `incLocatorsFrom` cancel effect of each other,
if they act only on free locators. -/
theorem subst_inc_cancel
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
    · rename_i n_is_not_free
      simp [Nat.lt_of_lt_of_le n_is_not_free le_0k]
      simp [substitute, Nat.lt_of_lt_of_le n_is_not_free le_0j]
    · rename_i n_is_free
      simp [le_nat_option_nat] at v_loc
      have n_is_free : zeroth_level ≤ n := Nat.ge_of_not_lt n_is_free
      have le_in: i + zeroth_level ≤ n :=
        (Nat.sub_add_cancel n_is_free) ▸ Nat.add_le_add_right v_loc zeroth_level
      have le_kn : k ≤ n := Nat.le_trans le_ki le_in
      have nlt_nk: ¬ n < k := fun x => Nat.lt_irrefl n (Nat.lt_of_lt_of_le x le_kn)
      simp [nlt_nk]
      have lt_jn1 : j < n + 1 := Nat.lt_succ_of_le (Nat.le_trans le_ji le_in)
      have nlt_n1j : ¬ n + 1 < j := fun x => Nat.lt_irrefl j (Nat.lt_trans lt_jn1 x)
      have neq_n1j : ¬ n + 1 = j := fun x => Nat.lt_irrefl j (x ▸ lt_jn1)
      simp [nlt_n1j, neq_n1j, Nat.add_sub_cancel]
  | dot t _ => by
    simp [substitute]
    apply subst_inc_cancel _ _ _ _ _ _ le_ji le_ki le_0j le_0k
      (by simp [min_free_loc] at v_loc ; exact v_loc)
  | app t _ u => by
    simp [min_free_loc] at v_loc
    have v_loc := le_min_option v_loc
    simp
    constructor <;> apply subst_inc_cancel _ _ _ _ _ _ le_ji le_ki le_0j le_0k
    · exact v_loc.left
    · exact v_loc.right
  | obj o => by
    simp
    exact subst_inc_cancel_Lst o _ _ _ _ _ le_ji le_ki le_0j le_0k v_loc

theorem subst_inc_cancel_Lst
  { lst : List Attr}
  ( bindings : Bindings lst)
  (u : Term)
  (j k i zeroth_level : Nat)
  (le_ji : j ≤ i + zeroth_level)
  (le_ki : k ≤ i + zeroth_level)
  (le_0j : zeroth_level ≤ j)
  (le_0k : zeroth_level ≤ k)
  (v_loc : le_nat_option_nat i (min_free_loc zeroth_level (obj bindings)))
  : bindings = substituteLst (j + 1, incLocators u) (incLocatorsFromLst (k + 1) bindings)
  := match bindings with
  | Bindings.nil => by simp
  | Bindings.cons _ _ void tail => by
    simp [min_free_loc] at *
    exact subst_inc_cancel_Lst tail u j k i zeroth_level le_ji le_ki le_0j le_0k v_loc
  | Bindings.cons _ _ (attached term) tail => by
    simp
    constructor
    · simp [min_free_loc] at v_loc
      have free_locs_term := (le_min_option v_loc).left
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
    · simp [min_free_loc] at v_loc
      have free_locs := le_min_option v_loc
      exact subst_inc_cancel_Lst tail _ _ _ _ _ le_ji le_ki le_0j le_0k free_locs.right
end

def lookup { lst : List Attr } (l : Bindings lst) (a : Attr) : Option OptionalAttr
  := match l with
    | Bindings.nil => none
    | Bindings.cons name _ opAttr tail =>
        if (name == a) then some opAttr
        else lookup tail a

theorem lookup_none_not_in
  { lst : List Attr }
  { l : Bindings lst }
  { a : Attr }
  (lookup_none : lookup l a = none)
  : a ∉ lst
  := fun a_in_lst => match lst with
    | [] => by contradiction
    | b :: bs => match l with
      | Bindings.cons _ _ opAttr tail =>
        dite
        (b = a)
        (fun eq => by simp [eq, lookup] at lookup_none)
        (fun neq => by
          simp [neq, lookup] at lookup_none
          have temp := lookup_none_not_in lookup_none
          match a_in_lst with
            | List.Mem.head _ => contradiction
            | List.Mem.tail _ memTail => contradiction
        )

theorem lookup_none_preserve
  { lst : List Attr }
  { l1 : Bindings lst }
  { a : Attr }
  (lookup_none : lookup l1 a = none)
  (l2 : Bindings lst)
  : (lookup l2 a = none)
  := match lst with
    | [] => match l2 with | Bindings.nil => by simp [lookup]
    | b :: bs => match l1, l2 with
      | Bindings.cons _ _ opAttr1 tail1, Bindings.cons _ _ opAttr2 tail2 => dite
        (b = a)
        (fun eq => by simp [lookup, eq] at lookup_none)
        (fun neq => by
          simp [lookup, neq] at lookup_none
          simp [lookup, neq]
          exact lookup_none_preserve lookup_none tail2
        )

def insert_φ
  { lst : List Attr }
  (l : Bindings lst)
  (a : Attr)
  (u : OptionalAttr)
  : (Bindings lst)
  := match l with
    | Bindings.nil => Bindings.nil
    | Bindings.cons name not_in opAttr tail =>
        if name == a then Bindings.cons name not_in u tail
        else Bindings.cons name not_in opAttr (insert_φ tail a u)

inductive IsAttached : { lst : List Attr } → Attr → Term → Bindings lst → Type where
  | zeroth_attached
    : { lst : List Attr }
    → (a : Attr)
    → (not_in : a ∉ lst)
    → (t : Term)
    → (l : Bindings lst)
    → IsAttached a t (Bindings.cons a not_in (attached t) l)
  | next_attached
    : { lst : List Attr }
    → (a : Attr)
    → (t : Term)
    → (l : Bindings lst)
    → (b : Attr)
    → (a ≠ b)
    → (not_in : b ∉ lst)
    → (u : OptionalAttr)
    → IsAttached a t l
    → IsAttached a t (Bindings.cons b not_in u l)

set_option linter.unusedVariables false
theorem isAttachedIsIn
  { lst : List Attr }
  { a : Attr }
  { t : Term }
  { l : Bindings lst }
  : IsAttached a t l
  → a ∈ lst
  | @IsAttached.zeroth_attached lst' _ _ _ _ => List.Mem.head lst'
  | IsAttached.next_attached _ _ _ b _ _ _ isAttached' =>
    List.Mem.tail b (isAttachedIsIn isAttached')
set_option linter.unusedVariables true

namespace Insert

  theorem insertAttachedStep
    { a b : Attr }
    { neq : a ≠ b }
    { t : Term }
    { lst : List Attr }
    { not_in : b ∉ lst }
    { u : OptionalAttr }
    { l : Bindings lst }
    : insert_φ (Bindings.cons b not_in u l) a (attached t)
        = Bindings.cons b not_in u (insert_φ l a (attached t))
    := by
      simp [insert_φ, neq]
      intro eq
      have neq' := neq.symm
      contradiction

  theorem insertAttached
    { a : Attr }
    { t : Term }
    { lst : List Attr }
    { l : Bindings lst }
    : IsAttached a t l
    → insert_φ l a (attached t) = l
      | IsAttached.zeroth_attached _ _ _ _ => by simp [insert_φ]
      | IsAttached.next_attached _ _ l b neq not_in u isAttached =>
          let step := @insertAttachedStep a b neq t _ not_in u _
          Eq.trans step (congrArg (Bindings.cons b not_in u) (insertAttached isAttached))

  theorem insertTwice
    {lst : List Attr}
    (l : Bindings lst)
    (a : Attr)
    (t t' : Term)
    : insert_φ (insert_φ l a (attached t')) a (attached t) = insert_φ l a (attached t)
    := match lst with
      | [] => match l with
        | Bindings.nil => by simp [insert_φ]
      | b :: bs => match l with
        | Bindings.cons _ not_in _ tail => dite (a = b)
          (fun eq => by simp [insert_φ, eq])
          (fun neq =>
            let neq' : b ≠ a := fun eq => neq eq.symm
            by  simp [insert_φ, neq']
                exact insertTwice tail a t t'
          )

  def insert_new_isAttached
    { lst : List Attr }
    { l : Bindings lst }
    { a : Attr }
    { t t' : Term}
    : IsAttached a t l → IsAttached a t' (insert_φ l a (attached t'))
    := fun isAttached => match isAttached with
      | IsAttached.zeroth_attached _ not_in _ _=> by
        simp [insert_φ]
        exact IsAttached.zeroth_attached _ _ _ _
      | IsAttached.next_attached _ _ l b neq not_in u new_isAttached => by
        have hypothesis : IsAttached a t' (insert_φ l a (attached t'))
          := insert_new_isAttached new_isAttached
        simp [insert_φ, neq.symm]
        exact IsAttached.next_attached a t' (insert_φ l a (attached t')) b neq not_in u hypothesis

end Insert

/-! ### Defition of regular and parallel reduction -/

/-- Evaluation [KS22, Fig. 1] -/
inductive Reduce : Term → Term → Type where
  | congOBJ
    : { t : Term }
    → { t' : Term }
    → (b : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → Reduce t t'
    → IsAttached b t l
    → Reduce (obj l) (obj (insert_φ l b (attached t')))
  | congDOT : ∀ t t' a, Reduce t t' → Reduce (dot t a) (dot t' a)
  | congAPPₗ : ∀ t t' u a, Reduce t t' → Reduce (app t a u) (app t' a u)
  | congAPPᵣ : ∀ t u u' a, Reduce u u' → Reduce (app t a u) (app t a u')
  | dot_c
    : { t : Term }
    → (t_c : Term)
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → t = obj l
    → lookup l c = some (attached t_c)
    → Reduce (dot t c) (substitute (0, t) t_c)
  | dot_cφ
    : { t : Term }
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → t = obj l
    → lookup l c = none
    → "φ" ∈ lst
    → Reduce (dot t c) (dot (dot t "φ") c)
  | app_c
    : (t u : Term)
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → t = obj l
    → lookup l c = some void
    → Reduce (app t c u) (obj (insert_φ l c (attached (incLocators u))))

mutual
  -- | tᵢ => tᵢ' for all i with ⟦ ... αᵢ ↦ tᵢ ... ⟧
  --   α's are given by `lst`
  inductive Premise : { lst : List Attr } → (l1 : Bindings lst) → (l2 : Bindings lst) → Type where
    | nil : Premise Bindings.nil Bindings.nil
    | consVoid
      : (a : Attr)
      → { lst : List Attr }
      → { l1 : Bindings lst }
      → { l2 : Bindings lst }
      → { not_in : a ∉ lst }
      → Premise l1 l2
      → Premise (Bindings.cons a not_in void l1) (Bindings.cons a not_in void l2)
    | consAttached
      : (a : Attr)
      → (t1 : Term)
      → (t2 : Term)
      → PReduce t1 t2
      → { lst : List Attr }
      → { l1 : Bindings lst }
      → { l2 : Bindings lst }
      → { not_in : a ∉ lst }
      → Premise l1 l2
      → Premise (Bindings.cons a not_in (attached t1) l1) (Bindings.cons a not_in (attached t2) l2)

  /-- Parallel reduction [KS22, Fig. 2] -/
  inductive PReduce : Term → Term → Type where
    | pcongOBJ
      : { lst : List Attr }
      → (l : Bindings lst)
      → (newAttrs : Bindings lst)
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
      → (l : Bindings lst)
      → PReduce t t'
      → t' = obj l
      → lookup l c = some (attached t_c)
      → PReduce (dot t c) (substitute (0, t') t_c)
    | pdot_cφ
      : { t t' : Term }
      → (c : Attr)
      → { lst : List Attr }
      → (l : Bindings lst)
      → PReduce t t'
      → t' = obj l
      → lookup l c = none
      → "φ" ∈ lst
      → PReduce (dot t c) (dot (dot t' "φ") c)
    | papp_c
      : { t t' u u' : Term }
      → (c : Attr)
      → { lst : List Attr }
      → (l : Bindings lst)
      → PReduce t t'
      → PReduce u u'
      → t' = obj l
      → lookup l c = some void
      → PReduce (app t c u) (obj (insert_φ l c (attached (incLocators u'))))
end

namespace PReduce

  mutual
    def reflexivePremise
      { lst : List Attr }
      (l : Bindings lst)
      : Premise l l
      := match l with
        | Bindings.nil => Premise.nil
        | Bindings.cons name not_in opAttr tail =>
            match opAttr with
              | void => Premise.consVoid name (reflexivePremise tail)
              | attached t => Premise.consAttached name t t (prefl t) (reflexivePremise tail)

/-- Reflexivity of parallel reduction [KS22, Proposition 3.3] -/
    def prefl : (t : Term) → PReduce t t
      := fun term => match term with
        | loc n => PReduce.pcong_ρ n
        | dot t a => PReduce.pcongDOT t t a (prefl t)
        | app t a u => PReduce.pcongAPP t t u u a (prefl t) (prefl u)
        | @obj lst l =>
            let premise := reflexivePremise l
            PReduce.pcongOBJ _ _ premise
  end

  def singlePremise
    { lst : List Attr }
    (l : Bindings lst)
    (a : Attr)
    (t : Term)
    (t' : Term)
    (isAttached : IsAttached a t l)
    (preduce : PReduce t t')
    : Premise l (insert_φ l a (attached t'))
    := match lst with
      | [] => match l with
        | Bindings.nil => Premise.nil
      | b :: bs => match isAttached with
        | IsAttached.zeroth_attached _ _ _ tail => match l with
          | Bindings.cons _ _ _ _ => by
              simp [insert_φ]
              exact Premise.consAttached b t t' preduce (reflexivePremise tail)
        | IsAttached.next_attached _ _ tail _ neq not_in u newIsAttached => match l with
          | Bindings.cons _ _ _ _ => by
              have neq' : b ≠ a := fun eq => neq eq.symm
              simp [insert_φ, neq']
              have premise := (singlePremise tail a t t' newIsAttached preduce)
              exact (match u with
                | void => Premise.consVoid b premise
                | attached u' => Premise.consAttached b u' u' (prefl u') premise
              )

  def singlePremiseInsert
    { lst : List Attr }
    { l1 l2 : Bindings lst }
    { a : Attr }
    { t1 t2 : Term }
    (preduce : PReduce t1 t2)
    (premise : Premise l1 l2)
    : Premise (insert_φ l1 a (attached t1)) (insert_φ l2 a (attached t2))
    := match premise with
      | Premise.nil => Premise.nil
      | Premise.consVoid b tail => dite
          (b = a)
          (fun eq => by
            simp [insert_φ, eq]
            exact Premise.consAttached b _ _ preduce tail
          )
          (fun neq => by
            simp [insert_φ, neq]
            exact Premise.consVoid b (singlePremiseInsert preduce tail)
          )
      | Premise.consAttached b t' t'' preduce' tail => dite
          (b = a)
          (fun eq => by
            simp [insert_φ, eq]
            exact Premise.consAttached b _ _ preduce tail
          )
          (fun neq => by
            simp [insert_φ, neq]
            exact Premise.consAttached b t' t'' preduce' (singlePremiseInsert preduce tail)
          )

  theorem lookup_void_premise
    { lst : List Attr }
    { l1 l2 : Bindings lst }
    { a : Attr }
    (lookup_void : lookup l1 a = some void)
    (premise : Premise l1 l2)
    : lookup l2 a = some void
    := match lst with
      | [] => match l1, l2 with | Bindings.nil, Bindings.nil => by contradiction
      | b :: bs => match l1, l2 with
          | Bindings.cons _ _ _ tail1, Bindings.cons _ _ _ tail2 => match premise with
            | Premise.consVoid _ premise_tail => dite
              (b = a)
              (fun eq => by simp [lookup, eq])
              (fun neq => by
                simp [lookup, neq] at lookup_void
                simp [lookup, neq]
                exact lookup_void_premise lookup_void premise_tail
              )
            | Premise.consAttached _ _ _ _ premise_tail => dite
              (b = a)
              (fun eq => by simp [lookup, eq] at lookup_void)
              (fun neq => by
                simp [lookup, neq] at lookup_void
                simp [lookup, neq]
                exact lookup_void_premise lookup_void premise_tail
              )

  inductive Pair : Prop → Type → Type where
    | pair
      : { p : Prop }
      → { t : Type }
      → (prop : p)
      → (val : t)
      → Pair p t

  def lookup_attached_premise
    { lst : List Attr }
    { l1 l2 : Bindings lst }
    { a : Attr }
    { u : Term }
    (lookup_attached : lookup l1 a = some (attached u))
    (premise : Premise l1 l2)
    : Σ u' : Term, Pair (lookup l2 a = some (attached u')) (PReduce u u')
    := match lst with
      | [] => match l1, l2 with | Bindings.nil, Bindings.nil => match premise with
        | Premise.nil => by
          simp [lookup]
          contradiction
      | b :: bs => match premise with
        | Premise.consVoid _ premise_tail => by
          simp [lookup]
          exact dite
            (b = a)
            (fun eq => by
              simp [lookup, eq] at lookup_attached
            )
            (fun neq => by
              simp [lookup, neq]
              simp [lookup, neq] at lookup_attached
              exact lookup_attached_premise (lookup_attached) premise_tail
            )
        | Premise.consAttached _ t1 t2 preduce premise_tail => by
          simp [lookup]
          exact dite
            (b = a)
            (fun eq => by
              simp [eq]
              simp [lookup, eq] at lookup_attached
              simp [lookup_attached] at preduce
              exact ⟨t2, Pair.pair rfl preduce⟩
            )
            (fun neq => by
              simp [neq]
              simp [lookup, neq] at lookup_attached
              exact lookup_attached_premise (lookup_attached) premise_tail
            )
end PReduce
open PReduce

def RedMany := ReflTransGen Reduce
def ParMany := ReflTransGen PReduce

infix:20 " ⇝ " => Reduce
infix:20 " ⇛ " => PReduce
infix:20 " ⇝* " => RedMany
infix:20 " ⇛* " => ParMany


/-! ### Equivalence of `⇛` and `⇝` -/

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (1)] -/
def reg_to_par {t t' : Term} : (t ⇝ t') → (t ⇛ t')
  | .congOBJ b l red isAttached =>
      .pcongOBJ
        l
        (insert_φ l b (attached _))
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

/-- Transitivity of `⇝*` [KS22, Lemma A.3] -/
def red_trans { t t' t'' : Term } (fi : t ⇝* t') (se : t' ⇝* t'') : (t ⇝* t'')
  := ReflTransGen.trans fi se

theorem notEqByMem
  { lst : List Attr }
  { a b : Attr }
  (a_is_in : a ∈ lst)
  (b_not_in : b ∉ lst)
  : a ≠ b
  := fun eq =>
    let memEq : List.Mem a lst = List.Mem b lst :=
      congrArg (fun x => Membership.mem lst x) eq
    b_not_in (Eq.mp memEq a_is_in)


def consBindingsRedMany
  { lst : List Attr}
  (a : Attr)
  { not_in_a : a ∉ lst }
  (u_a  : OptionalAttr)
  { l1 l2 : Bindings lst }
  (reds : (obj l1) ⇝* (obj l2))
  : obj (Bindings.cons a not_in_a u_a l1) ⇝*
    obj (Bindings.cons a not_in_a u_a l2)
  := by
    generalize h : obj l1 = t1
    generalize h' : obj l2 = t2
    rw [h, h'] at reds
    induction reds generalizing l1 l2 with
    | refl =>
      subst h ; simp at h' ; simp [h'] ; exact .refl
    | head =>
      subst h h'
      rename_i t_i red redmany ih
      match red with
      | Reduce.congOBJ attr _ inner_red isAttached =>
        rename_i ti1 ti2
        have tail_cons := @ih (insert_φ l1 attr (attached ti2)) l2 rfl rfl
        have neq := (notEqByMem (isAttachedIsIn isAttached) not_in_a)
        have isAttached_cons : IsAttached attr ti1 (Bindings.cons a not_in_a u_a l1) :=
        IsAttached.next_attached attr ti1 l1 a neq not_in_a u_a isAttached
        have head_cons := Reduce.congOBJ attr _ inner_red isAttached_cons
        simp [insert_φ, neq.symm] at head_cons
        exact ReflTransGen.head head_cons tail_cons

/-- Congruence for `⇝*` in OBJ [KS22, Lemma A.4 (1)] -/
def congOBJClos
  { t t' : Term }
  { b : Attr }
  { lst : List Attr }
  { l : Bindings lst }
  : (t ⇝* t')
  → IsAttached b t l
  → (obj l ⇝* obj (insert_φ l b (attached t')))
  := fun red_tt' isAttached => match red_tt' with
    | ReflTransGen.refl =>
      Eq.ndrec (ReflTransGen.refl) (congrArg obj (Eq.symm (Insert.insertAttached isAttached)))
    | ReflTransGen.head red redMany => by
      rename_i t_i
      have ind_hypothesis
        : obj (insert_φ l b (attached t_i))
          ⇝* obj (insert_φ (insert_φ l b (attached t_i)) b (attached t'))
        := (congOBJClos redMany (Insert.insert_new_isAttached isAttached))
      exact (ReflTransGen.head
        (Reduce.congOBJ b l red isAttached)
        (Eq.ndrec ind_hypothesis
        (congrArg obj (Insert.insertTwice l b t' t_i))))

/-- Congruence for `⇝*` in DOT [KS22, Lemma A.4 (2)] -/
def congDotClos
  { t t' : Term }
  { a : Attr }
  : (t ⇝* t') → ((dot t a) ⇝* (dot t' a))
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head lm mn_many => by
    rename_i m
    exact (ReflTransGen.head (Reduce.congDOT t m a lm) (congDotClos mn_many))

/-- Congruence for `⇝*` in APPₗ [KS22, Lemma A.4 (3)] -/
def congAPPₗClos
  { t t' u : Term }
  { a : Attr }
  : (t ⇝* t') → ((app t a u) ⇝* (app t' a u))
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head lm mn_many => by
    rename_i m
    exact (ReflTransGen.head (Reduce.congAPPₗ t m u a lm) (congAPPₗClos mn_many))

/-- Congruence for `⇝*` in APPᵣ [KS22, Lemma A.4 (4)] -/
def congAPPᵣClos
  { t u u' : Term }
  { a : Attr }
  : (u ⇝* u') → ((app t a u) ⇝* (app t a u'))
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head lm mn_many => by
    rename_i m
    exact ReflTransGen.head (Reduce.congAPPᵣ t u m a lm) (congAPPᵣClos mn_many)

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (3)] -/
def par_to_redMany {t t' : Term} : (t ⇛ t') → (t ⇝* t')
  | @PReduce.pcongOBJ lst l l' premise =>
    let rec fold_premise
      { lst : List Attr }
      { al al' : Bindings lst }
      (premise : Premise al al')
      : (obj al) ⇝* (obj al')
      := match lst with
        | [] => match al, al' with
          | Bindings.nil, Bindings.nil => ReflTransGen.refl
        | a :: as => match al, al' with
          | Bindings.cons _ not_in u tail, Bindings.cons _ _ u' tail' => match premise with
            | Premise.consVoid _ premiseTail =>
              consBindingsRedMany a void (fold_premise premiseTail)
            | @Premise.consAttached _ t1 t2 preduce _ l1 l2 not_in premiseTail => by
                suffices temp
                  : obj (insert_φ (Bindings.cons a not_in (attached t1) l1) a (attached t2)) ⇝*
                  obj (Bindings.cons a _ (attached t2) l2) from
                  (red_trans
                    (congOBJClos (par_to_redMany preduce) (IsAttached.zeroth_attached a _ t1 l1))
                    (temp))
                simp [insert_φ]
                exact consBindingsRedMany a (attached t2) (fold_premise premiseTail)
    fold_premise premise
  | .pcong_ρ n => ReflTransGen.refl
  | .pcongDOT t t' a prtt' => congDotClos (par_to_redMany prtt')
  | .pcongAPP t t' u u' a prtt' pruu' => red_trans
    (congAPPₗClos (par_to_redMany prtt'))
    (congAPPᵣClos (par_to_redMany pruu'))
  | PReduce.pdot_c t_c c l preduce eq lookup_eq =>
    let tc_t'c_many := congDotClos (par_to_redMany preduce)
    let tc_dispatch := Reduce.dot_c t_c c l eq lookup_eq
    let tc_dispatch_clos := ReflTransGen.head tc_dispatch ReflTransGen.refl
    red_trans tc_t'c_many tc_dispatch_clos
  | PReduce.pdot_cφ c l preduce eq lookup_eq isAttr =>
    let tc_t'c_many := congDotClos (par_to_redMany preduce)
    let tφc_dispatch := Reduce.dot_cφ c l eq lookup_eq isAttr
    let tφc_dispatch_clos := ReflTransGen.head tφc_dispatch ReflTransGen.refl
    red_trans tc_t'c_many tφc_dispatch_clos
  | @PReduce.papp_c t t' u u' c lst l prtt' pruu' path_t'_obj_lst path_lst_c_void =>
    let tu_t'u_many := congAPPₗClos (par_to_redMany prtt')
    let t'u_t'u'_many := congAPPᵣClos (par_to_redMany pruu')
    let tu_t'u'_many := red_trans tu_t'u_many t'u_t'u'_many
    let tu_app := Reduce.app_c t' u' c l path_t'_obj_lst path_lst_c_void
    let tu_app_clos := ReflTransGen.head tu_app ReflTransGen.refl
    red_trans tu_t'u'_many tu_app_clos

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (4)] -/
def parMany_to_redMany {t t' : Term} : (t ⇛* t') → (t ⇝* t')
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head red reds => red_trans (par_to_redMany red) (parMany_to_redMany reds)

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (2)] -/
def redMany_to_parMany {t t' : Term} : (t ⇝* t') → (t ⇛* t')
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head red reds => ReflTransGen.head (reg_to_par red) (redMany_to_parMany reds)

/-! ### Substitution Lemma -/
mutual
/-- Increment swap [KS22, Lemma A.9] -/
theorem inc_swap
  ( i j : Nat)
  ( le_ij : i ≤ j)
  ( t : Term)
  : incLocatorsFrom i (incLocatorsFrom j t) = incLocatorsFrom (j + 1) (incLocatorsFrom i t)
  := match t with
    | loc k => by
      simp [incLocatorsFrom]
      split
      · rename_i lt_kj
        simp [incLocatorsFrom]
        split
        · rename_i lt_ki
          have lt_kj1 : k < j + 1 := Nat.lt_trans lt_kj (Nat.lt_succ_self j)
          simp [incLocatorsFrom, lt_kj1]
        · rename_i nlt_ki
          simp [incLocatorsFrom, Nat.succ_lt_succ lt_kj]
      · rename_i nlt_kj
        have le_ik : i ≤ k := Nat.le_trans le_ij (Nat.ge_of_not_lt nlt_kj)
        have nlt_k1i: ¬ k + 1 < i :=
          fun x => absurd
            ((Nat.lt_trans (Nat.lt_of_le_of_lt le_ik (Nat.lt_succ_self k)) x)) (Nat.lt_irrefl i)
        have nlt_ki : ¬ k < i := fun x => absurd le_ik (Nat.not_le_of_gt x)
        have nlt_k1j1 : ¬ k + 1 < j + 1 := fun x => nlt_kj (Nat.lt_of_succ_lt_succ x)
        simp [incLocatorsFrom, nlt_k1i, nlt_ki, nlt_k1j1]
    | dot s a => by
      simp
      exact inc_swap i j le_ij s
    | app s a u => by
      simp
      constructor
      · exact inc_swap i j le_ij s
      · exact inc_swap i j le_ij u
    | obj o => by
      simp
      exact inc_swap_Lst i j le_ij o

theorem inc_swap_Lst
  ( i j : Nat)
  ( le_ij : i ≤ j)
  { lst : List Attr}
  ( o : Bindings lst)
  : incLocatorsFromLst (i + 1) (incLocatorsFromLst (j + 1) o) =
  incLocatorsFromLst (j + 1 + 1) (incLocatorsFromLst (i + 1) o)
  := match o with
  | Bindings.nil => by simp
  | Bindings.cons _ _ void tail => by
    simp
    exact inc_swap_Lst i j le_ij tail
  | Bindings.cons _ _ (attached t) tail => by
    simp
    constructor
    · exact inc_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ij) t
    · exact inc_swap_Lst i j le_ij tail
end

mutual
/-- Increment and substitution swap [KS22, Lemma A.8] -/
theorem subst_inc_swap
  ( i j : Nat)
  ( le_ji : j ≤ i)
  ( t u : Term)
  : substitute (i+1, incLocatorsFrom j u) (incLocatorsFrom j t) =
    (incLocatorsFrom j (substitute (i, u) t))
  := match t with
    | loc k => by
      simp [substitute, incLocatorsFrom]
      split
      · rename_i lt_kj
        have lt_ki: k < i := Nat.lt_of_lt_of_le lt_kj le_ji
        have lt_ki1 : k < i + 1 := Nat.lt_succ_of_le (Nat.le_of_lt lt_ki)
        simp [substitute, lt_ki1, lt_ki, incLocatorsFrom, lt_kj]
      · rename_i nlt_kj
        split
        · rename_i lt_ki
          have lt_k1i1 : k + 1 < i + 1 := Nat.succ_lt_succ lt_ki
          simp [substitute, incLocatorsFrom, lt_k1i1, nlt_kj]
        · rename_i nlt_ki
          have nlt_k1i1 : ¬k + 1 < i + 1
            := fun x => absurd (Nat.lt_of_succ_lt_succ x) nlt_ki
          simp [substitute, nlt_k1i1]
          split
          · rename_i eq_ki
            rfl
          · rename_i neq_ki
            have neq_ik : ¬ i = k := fun eq => neq_ki eq.symm
            have lt_ik : i < k := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt nlt_ki) neq_ik
            have lt_jk : j < k := Nat.lt_of_le_of_lt le_ji lt_ik
            have le_k1 : 1 ≤ k := Nat.succ_le_of_lt
              (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
            have k0 : k - 1 + 1 = k := Nat.sub_add_cancel le_k1
            have lt_j1k1 : j + 1 < k + 1 := Nat.succ_lt_succ lt_jk
            have le_j1k : j + 1 ≤ k := Nat.le_of_lt_succ lt_j1k1
            have le_jk1 := Nat.le_of_succ_le_succ (k0.symm ▸ le_j1k)
            have nlt_jk1: ¬k - 1 < j := fun x => absurd le_jk1 (Nat.not_le_of_gt x)
            simp [incLocatorsFrom, nlt_jk1, k0, Nat.add_sub_cancel]
    | dot s a => by
      simp [substitute, incLocatorsFrom]
      exact subst_inc_swap i j le_ji s u
    | app s₁ a s₂ => by
      simp [substitute, incLocatorsFrom]
      constructor
      · exact subst_inc_swap i j le_ji s₁ u
      · exact subst_inc_swap i j le_ji s₂ u
    | obj o => by
      simp
      exact subst_inc_swap_Lst i j le_ji o u

theorem subst_inc_swap_Lst
  ( i j : Nat)
  ( le_ji : j ≤ i)
  { lst : List Attr}
  ( o : Bindings lst)
  ( u : Term)
  : substituteLst (i + 1 + 1, incLocators (incLocatorsFrom j u)) (incLocatorsFromLst (j + 1) o) =
  incLocatorsFromLst (j + 1) (substituteLst (i + 1, incLocators u) o)
  := by match o with
  | Bindings.nil => simp
  | Bindings.cons _ _ void tail =>
    simp
    exact subst_inc_swap_Lst i j le_ji tail u
  | Bindings.cons _ _ (attached t) tail =>
    simp
    constructor
    · simp [incLocators, inc_swap]
      rw [← incLocators]
      exact subst_inc_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ji) t (incLocators u)
    · exact subst_inc_swap_Lst i j le_ji tail u
end

mutual
/-- Increment and substitution swap, dual to A.8 -/
theorem inc_subst_swap
  ( i j : Nat)
  ( le_ji : j ≤ i)
  ( t u : Term)
  : incLocatorsFrom i (substitute (j, u) t) =
    substitute (j, incLocatorsFrom i u) (incLocatorsFrom (i + 1) t)
  := match t with
    | loc k => by
      simp
      split
      · rename_i lt_kj
        have lt_ki: k < i := Nat.lt_of_lt_of_le lt_kj le_ji
        have lt_ki1 : k < i + 1 := Nat.lt_succ_of_le (Nat.le_of_lt lt_ki)
        simp [lt_ki1, lt_ki, lt_kj]
      · rename_i nlt_kj
        split
        · rename_i eq_kj
          simp [eq_kj, Nat.lt_succ_of_le le_ji]
        · rename_i neq_kj
          have lt_jk : j < k
            := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt nlt_kj) (fun x => neq_kj x.symm)
          have le_k1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
          have k0 : k - 1 + 1 = k := Nat.sub_add_cancel le_k1
          split
          · rename_i lt_ki1
            have lt_k1i : k - 1 < i := Nat.lt_of_succ_lt_succ (k0.symm ▸ lt_ki1)
            simp [nlt_kj, neq_kj, lt_k1i]
          · rename_i nlt_ki1
            have nlt_k1i : ¬ k - 1 < i := fun x => by
              have lt_ki1 := Nat.add_lt_add_right x 1
              simp [Nat.sub_add_cancel le_k1] at lt_ki1
              exact nlt_ki1 lt_ki1
            have lt_ik : i < k := Nat.lt_of_succ_le (Nat.ge_of_not_lt nlt_ki1)
            have lt_jk1 : j < k + 1
              := Nat.lt_trans (Nat.lt_of_le_of_lt le_ji lt_ik) (Nat.lt_succ_self k)
            have nlt_k1j : ¬ k + 1 < j := fun x =>
              (Nat.lt_irrefl j) (Nat.lt_trans lt_jk1 x)
            have neq_k1j : ¬ k + 1 = j := fun x =>
              (Nat.lt_irrefl j) (x ▸ lt_jk1 )
            simp [nlt_k1i, neq_k1j, nlt_k1j, k0, Nat.add_sub_cancel]
    | dot s a => by
      simp
      exact inc_subst_swap i j le_ji s u
    | app s₁ a s₂ => by
      simp
      constructor
      · exact inc_subst_swap i j le_ji s₁ u
      · exact inc_subst_swap i j le_ji s₂ u
    | obj o => by
      simp
      exact inc_subst_swap_Lst i j le_ji o u

theorem inc_subst_swap_Lst
  ( i j : Nat)
  ( le_ji : j ≤ i)
  { lst : List Attr}
  ( o : Bindings lst)
  ( u : Term)
  : incLocatorsFromLst (i + 1) (substituteLst (j + 1, incLocators u) o) =
  substituteLst (j + 1, incLocators (incLocatorsFrom i u)) (incLocatorsFromLst (i + 1 + 1) o)
  := by match o with
  | Bindings.nil => simp
  | Bindings.cons _ _ void tail =>
    simp
    exact inc_subst_swap_Lst i j le_ji tail u
  | Bindings.cons _ _ (attached t) tail =>
    simp
    constructor
    · simp [incLocators, inc_swap]
      rw [← incLocators]
      exact inc_subst_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ji) t (incLocators u)
    · exact inc_subst_swap_Lst i j le_ji tail u
end

mutual
/-- Substitutions swap [KS22, Lemma A.7] -/
theorem subst_swap
  ( i j : Nat)
  ( le_ji : j ≤ i)
  ( t u v : Term)
  ( free_locs_v : le_nat_option_nat i (min_free_loc 0 v))
  : substitute (i, v) (substitute (j, u) t) =
    substitute (j, substitute (i, v) u) (substitute (i+1, incLocators v) t)
  := match t with
    | loc k => by
        simp
        split
        · rename_i lt_kj
          have lt_ki : k < i := Nat.le_trans lt_kj le_ji
          have lt_ki1 : k < i + 1 := Nat.le_step lt_ki
          simp [lt_kj, lt_ki, lt_ki1]
          -- case k < j
        · rename_i not_lt
          have le_jk: j ≤ k := Nat.ge_of_not_lt not_lt
          split
          · rename_i eq_kj
            have lt_ji1 : j < i + 1 :=  Nat.lt_succ_of_le le_ji
            simp [eq_kj, lt_ji1]
            -- case k == j
          · rename_i neq_kj
            have neq_jk : ¬j = k := fun eq => neq_kj eq.symm
            have lt_jk : j < k := Nat.lt_of_le_of_ne le_jk neq_jk
            simp
            have le_k1: 1 ≤ k := Nat.succ_le_of_lt
              (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
            split
            · rename_i le_k1i
              have lt_ki1: k < i + 1 := by
                have temp := Nat.add_lt_add_right le_k1i 1
                simp [Nat.sub_add_cancel le_k1] at temp
                exact temp
              have nlt_kj : ¬ k < j := fun lt_kj => Nat.lt_irrefl k (Nat.lt_trans lt_kj lt_jk)
              simp [lt_ki1, neq_kj, nlt_kj]
              -- case j < k ≤ i
            · rename_i nlt_k1i
              split
              · rename_i eq_k1i
                have eq_ki1 : k = i + 1 := by
                  have temp : k - 1 + 1 = i + 1 := congrArg Nat.succ eq_k1i
                  simp [Nat.sub_add_cancel le_k1] at temp
                  exact temp
                simp [eq_ki1]
                exact subst_inc_cancel
                  v _
                  j 0 i 0
                  le_ji
                  (Nat.zero_le i)
                  (Nat.zero_le j)
                  (Nat.zero_le 0)
                  free_locs_v
              · rename_i neq_k1i
                have lt_ik1: i < k - 1
                  := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt (nlt_k1i)) (fun x => neq_k1i x.symm)
                have lt_i1k : i + 1 < k := by
                  have := Nat.add_lt_add_right lt_ik1 1
                  simp [Nat.sub_add_cancel le_k1] at this
                  exact this
                have nle_ki1 : ¬ k < i + 1 := fun x => Nat.lt_irrefl k (Nat.lt_trans x lt_i1k)
                have neq_ki1 : ¬ k = i + 1 := fun x => Nat.lt_irrefl k (x ▸ lt_i1k)
                simp [nle_ki1, neq_ki1]
                have nlt_k1j : ¬ k - 1 < j := fun x => Nat.lt_irrefl j
                  (Nat.lt_trans (Nat.lt_of_le_of_lt le_ji lt_ik1) x)
                have neq : ¬ k - 1 = j := fun x => Nat.lt_irrefl j
                  (Nat.lt_of_le_of_lt le_ji (x ▸ lt_ik1))
                simp [nlt_k1j, neq]
    | dot s a => by
      simp
      apply subst_swap _ _ le_ji _ _ _ free_locs_v
    | app s₁ a s₂ => by
      simp
      constructor <;> apply subst_swap _ _ le_ji _ _ _ free_locs_v
    | obj o => by
      simp
      exact subst_swap_Lst i j le_ji o u v free_locs_v

theorem subst_swap_Lst
  ( i j : Nat)
  ( le_ji : j ≤ i)
  { lst : List Attr}
  ( o : Bindings lst)
  ( u v : Term)
  ( free_locs_v : le_nat_option_nat i (min_free_loc 0 v))
  : substituteLst (i + 1, incLocators v) (substituteLst (j + 1, incLocators u) o) =
    substituteLst
      (j + 1, incLocators (substitute (i, v) u))
      (substituteLst (i + 1 + 1, incLocators (incLocators v)) o)
  := by match o with
  | Bindings.nil => simp
  | Bindings.cons _ _ void tail =>
    simp
    exact subst_swap_Lst i j le_ji tail u v free_locs_v
  | Bindings.cons _ _ (attached t) tail =>
    simp
    constructor
    · simp [incLocators]
      simp [← subst_inc_swap]
      rw [← incLocators]
      exact subst_swap (i+1) (j+1) (Nat.add_le_add_right le_ji 1)
        t (incLocators u) (incLocators v) (min_free_loc_inc free_locs_v)
    · exact subst_swap_Lst i j le_ji tail u v free_locs_v
end

theorem lookup_inc_attached
  (t : Term)
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some (attached t))
  : lookup (incLocatorsFromLst i l) c = some (attached (incLocatorsFrom i t))
  := by match l with
  | Bindings.nil => contradiction
  | Bindings.cons name _ void tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · simp at lookup_eq
    · rename_i neq
      simp [lookup, neq]
      exact (lookup_inc_attached t i c tail lookup_eq)
  | Bindings.cons name _ (attached _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · rename_i eq
      simp at lookup_eq
      simp [lookup_eq]
      simp [lookup_eq, lookup, eq]
    · rename_i neq
      simp [lookup, neq]
      exact (lookup_inc_attached t i c tail lookup_eq)

theorem lookup_inc_void
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some void)
  : lookup (incLocatorsFromLst i l) c = some void
  := by match l with
  | Bindings.nil => contradiction
  | Bindings.cons name _ void tail =>
    simp [lookup] at lookup_eq
    exact (dite (name = c)
      (fun lookup_eq => by
        simp [lookup, lookup_eq]))
      (fun neq => by
        simp [lookup, neq]
        exact (lookup_inc_void i c tail (lookup_eq neq)))

  | Bindings.cons name _ (attached _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · simp at lookup_eq
    · rename_i neq
      simp [lookup, neq]
      exact (lookup_inc_void i c tail lookup_eq)

theorem lookup_inc_none
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = none)
  : lookup (incLocatorsFromLst i l) c = none
  := by match l with
  | Bindings.nil => simp ; assumption
  | Bindings.cons name _ u tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · contradiction
    · rename_i neq
      cases u
      repeat simp [lookup, neq] ; exact (lookup_inc_none i c tail lookup_eq)

theorem inc_insert
  { i : Nat }
  { c : Attr }
  { lst : List Attr }
  { l : Bindings lst }
  { v : Term}
  : (insert_φ (incLocatorsFromLst (i + 1) l) c (attached (incLocators (incLocatorsFrom i v)))) =
  (incLocatorsFromLst (i + 1) (insert_φ l c (attached (incLocators v))))
  := match l with
  | Bindings.nil => by
    simp [insert_φ]
  | Bindings.cons a not_in u _ => by
    cases u
    repeat
      simp [insert_φ]
      split
      · simp
        rw [incLocators]
        simp [inc_swap]
      · simp
        apply inc_insert

mutual
/-- Increment of locators preserves parallel reduction. -/
def preduce_incLocatorsFrom
  { t t' : Term}
  ( i : Nat)
  : ( t ⇛ t') → (incLocatorsFrom i t ⇛ incLocatorsFrom i t')
  | .pcongOBJ bnds bnds' premise => by
    simp
    exact PReduce.pcongOBJ (incLocatorsFromLst (i + 1) bnds)
      (incLocatorsFromLst (i + 1) bnds') (preduce_incLocatorsFrom_Lst i premise)
  | .pcong_ρ n =>  prefl (incLocatorsFrom i (loc n))
  | .pcongAPP t t' u u' a tt' uu' => by
    simp
    apply PReduce.pcongAPP
    · exact preduce_incLocatorsFrom i tt'
    · exact preduce_incLocatorsFrom i uu'
  | .pcongDOT t t' a tt' => by
    simp
    apply PReduce.pcongDOT
    exact preduce_incLocatorsFrom i tt'
  | @PReduce.pdot_c s s' t_c c lst l ss' eq lookup_eq => by
    simp [inc_subst_swap]
    exact @PReduce.pdot_c
      (incLocatorsFrom i s)
      (incLocatorsFrom i s')
      _
      c
      lst
      (incLocatorsFromLst (i+1) l)
      (preduce_incLocatorsFrom i ss')
      (by simp [eq])
      (lookup_inc_attached t_c (i+1) c l lookup_eq)
  | @PReduce.pdot_cφ s s' c lst l ss' eq lookup_eq is_attr => by
    simp
    exact @PReduce.pdot_cφ
      (incLocatorsFrom i s)
      (incLocatorsFrom i s')
      c
      lst
      (incLocatorsFromLst (i + 1) l)
      (preduce_incLocatorsFrom i ss')
      (by rw [eq, incLocatorsFrom])
      (lookup_inc_none (i+1) c l lookup_eq)
      (is_attr)
  | @PReduce.papp_c s s' v v' c lst l ss' vv' eq lookup_eq => by
    simp [← inc_insert]
    exact @PReduce.papp_c
      (incLocatorsFrom i s)
      (incLocatorsFrom i s')
      (incLocatorsFrom i v)
      (incLocatorsFrom i v')
      c
      lst
      (incLocatorsFromLst (i + 1) l)
      (preduce_incLocatorsFrom i ss')
      (preduce_incLocatorsFrom i vv')
      (by rw [eq, incLocatorsFrom])
      (lookup_inc_void (i+1) c l lookup_eq)

def preduce_incLocatorsFrom_Lst
  { lst : List Attr }
  { bnds bnds' : Bindings lst }
  (i : Nat)
  (premise : Premise bnds bnds')
  : Premise (incLocatorsFromLst (i + 1) bnds) (incLocatorsFromLst (i + 1) bnds')
  :=  match lst with
  | [] => match bnds, bnds' with
    | Bindings.nil, Bindings.nil => by
      simp
      exact Premise.nil
  | _ :: as => match premise with
    | Premise.consVoid a tail => by
      simp
      exact Premise.consVoid a (preduce_incLocatorsFrom_Lst i tail)
    | Premise.consAttached a t1 t2 preduce tail => by
      simp
      exact Premise.consAttached
        a
        _
        _
        (preduce_incLocatorsFrom (i+1) preduce)
        (preduce_incLocatorsFrom_Lst i tail)
end

def get_premise
  { attrs : List Attr }
  { bnds bnds' : Bindings attrs }
  (preduce : obj bnds ⇛ obj bnds')
  : Premise bnds bnds'
  := match preduce with
    | PReduce.pcongOBJ _ _ premise => premise

theorem lookup_subst_attached
  (t : Term)
  {u : Term}
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some (attached t))
  : lookup (substituteLst (i, u) l) c = some (attached (substitute (i, u) t))
  := by match l with
  | Bindings.nil => contradiction
  | Bindings.cons name _ void tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · simp at lookup_eq
    · rename_i neq
      simp [lookup, neq]
      exact (lookup_subst_attached t i c tail lookup_eq)
  | Bindings.cons name _ (attached _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · rename_i eq
      simp at lookup_eq
      simp [lookup_eq]
      simp [lookup_eq, lookup, eq]
    · rename_i neq
      simp [lookup, neq]
      exact (lookup_subst_attached t i c tail lookup_eq)

theorem lookup_subst_void
  {u : Term}
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some void)
  : lookup (substituteLst (i, u) l) c = some void
  := by match l with
  | Bindings.nil => contradiction
  | Bindings.cons name _ void tail =>
    simp [lookup] at lookup_eq
    exact (dite (name = c)
      (fun lookup_eq => by
        simp [lookup, lookup_eq]))
      (fun neq => by
        simp [lookup, neq]
        exact (lookup_subst_void i c tail (lookup_eq neq)))
  | Bindings.cons name _ (attached _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · simp at lookup_eq
    · rename_i neq
      simp [lookup, neq]
      exact (lookup_subst_void i c tail lookup_eq)

theorem lookup_subst_none
  {u : Term}
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = none)
  : lookup (substituteLst (i, u) l) c = none
  := by match l with
  | Bindings.nil => simp ; assumption
  | Bindings.cons name _ u tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    · contradiction
    · rename_i neq
      cases u
      repeat simp [lookup, neq] ; exact (lookup_subst_none i c tail lookup_eq)

theorem subst_insert
  { i : Nat }
  { c : Attr }
  { lst : List Attr }
  { l : Bindings lst }
  { u v : Term}
  : insert_φ
      (substituteLst (i + 1, incLocators u) l) c
      (attached (incLocators (substitute (i, u) v)))
    = substituteLst (i + 1, incLocators u) (insert_φ l c (attached (incLocators v)))
  := match l with
  | Bindings.nil => by
    simp [insert_φ]
  | Bindings.cons a not_in u _ => by
    cases u
    repeat
      simp [insert_φ]
      split
      · simp
        rw [incLocators]
        simp [subst_inc_swap]
      · simp
        apply subst_insert

mutual
/-- Substitution Lemma [KS22, Lemma 3.5] -/
def substitution_lemma
  ( i : Nat )
  { t t' u u' : Term }
  (tt' : t ⇛ t')
  (uu' : u ⇛ u')
  (min_free_locs_u' : le_nat_option_nat i (min_free_loc 0 u'))
  : substitute (i, u) t ⇛ substitute (i, u') t'
  := match tt' with
  | @PReduce.pcongOBJ attrs bnds bnds' premise => by
    simp
    exact PReduce.pcongOBJ
      (substituteLst (i + 1, incLocators u) bnds)
        (substituteLst (i + 1, incLocators u') bnds')
        (substitution_lemma_Lst i premise uu' min_free_locs_u')
  | .pcong_ρ n => by
    simp
    exact dite (n < i)
      (fun less => by
        simp [less]
        exact PReduce.pcong_ρ n
      )
      (fun not_less =>
        dite (n = i)
          (fun eq => by
            have obvious : ¬ i < i := Nat.lt_irrefl i
            simp [not_less, eq, obvious]
            exact uu'
          )
          (fun not_eq => by
            simp [not_less, not_eq]
            exact PReduce.pcong_ρ (n - 1)
          )
      )
  | .pcongDOT lt lt' a preduce => by
    simp
    exact PReduce.pcongDOT
      (substitute (i, u) lt)
      (substitute (i, u') lt')
      a
      (substitution_lemma i preduce uu' (by assumption))
  | .pcongAPP lt lt' lu lu' a preduce_t preduce_u => by
    simp
    exact PReduce.pcongAPP
      (substitute (i, u) lt)
      (substitute (i, u') lt')
      (substitute (i, u) lu)
      (substitute (i, u') lu')
      a
      (substitution_lemma i preduce_t uu' (by assumption))
      (substitution_lemma i preduce_u uu' (by assumption))
  | @PReduce.pdot_c s s' t_c c lst l ss' eq lookup_eq => by
    have dot_subst : dot (substitute (i, u) s) c ⇛
      substitute (0, substitute (i, u') s') (substitute (i+1, incLocators u') t_c)
    := @PReduce.pdot_c
      (substitute (i, u) s)
      (substitute (i, u') s')
      (substitute (i+1, incLocators u') t_c)
      c
      lst
      (substituteLst (i+1, incLocators u') l)
      (substitution_lemma i ss' uu' (by assumption))
      (by rw [eq, substitute])
      (lookup_subst_attached t_c (i+1) c l lookup_eq)
    have := (subst_swap i 0 (Nat.zero_le i) t_c s' u' ((by assumption))).symm
    simp [this] at dot_subst
    simp
    exact dot_subst
  | @PReduce.pdot_cφ s s' c lst l ss' eq lookup_eq is_attr => by
    simp
    exact @PReduce.pdot_cφ
      (substitute (i, u) s)
      (substitute (i, u') s')
      c
      lst
      (substituteLst (i+1, incLocators u') l)
      (substitution_lemma i ss' uu' (by assumption))
      (by rw [eq, substitute])
      (lookup_subst_none (i+1) c l lookup_eq)
      (is_attr)
  | @PReduce.papp_c s s' v v' c lst l ss' vv' eq lookup_eq => by
    simp [← subst_insert]
    exact @PReduce.papp_c
      (substitute (i, u) s)
      (substitute (i, u') s')
      (substitute (i, u) v)
      (substitute (i, u') v')
      c
      lst
      (substituteLst (i+1, incLocators u') l)
      (substitution_lemma i ss' uu' (by assumption))
      (substitution_lemma i vv' uu' ((by assumption)))
      (by rw [eq, substitute])
      (lookup_subst_void (i+1) c l lookup_eq)

def substitution_lemma_Lst
  ( i : Nat )
  { lst : List Attr }
  { l l' : Bindings lst }
  (premise : Premise l l')
  { u u' : Term }
  (uu' : u ⇛ u')
  (min_free_locs_u : le_nat_option_nat i (min_free_loc 0 u'))
  : Premise (substituteLst (i + 1, incLocators u) l) (substituteLst (i + 1, incLocators u') l')
  := by match premise with
  | Premise.nil => simp ; exact Premise.nil
  | Premise.consVoid _ premise_tail =>
    simp
    apply Premise.consVoid
    exact substitution_lemma_Lst i premise_tail uu' min_free_locs_u
  | Premise.consAttached _ t1 t2 preduce premise_tail =>
    simp
    apply Premise.consAttached
    · apply substitution_lemma
      exact preduce
      exact preduce_incLocatorsFrom 0 uu'
      exact min_free_loc_inc min_free_locs_u
    · exact substitution_lemma_Lst i premise_tail uu' min_free_locs_u
end

/-! ### Complete Development -/

mutual
/-- Complete Development [KS22, Definition 3.6] -/
@[simp]
def complete_development : Term → Term
  | loc n => loc n
  | dot t a => match (complete_development t) with
    | @obj attrs bnds => match (lookup bnds a) with
      | some (attached t_a) => (substitute (0, (obj bnds)) t_a)
      | some void => dot (obj bnds) a
      | none => if ("φ" ∈ attrs) then dot (dot (obj bnds) "φ") a else dot (obj bnds) a
    | t' => dot t' a
  | app t a u => match (complete_development t) with
    | @obj _ bnds => match (lookup bnds a) with
      | some void => obj (insert_φ bnds a (attached (incLocators (complete_development u))))
      | _ => app (obj bnds) a (complete_development u)
    | _ => app (complete_development t) a (complete_development u)
  | obj bnds => obj (complete_developmentLst bnds)
@[simp]
def complete_developmentLst {lst : List Attr} : Bindings lst → Bindings lst
  | Bindings.nil => Bindings.nil
  | Bindings.cons a lst void tail => Bindings.cons a lst void (complete_developmentLst tail)
  | Bindings.cons a lst (attached t) tail =>
    Bindings.cons a lst (attached (complete_development t)) (complete_developmentLst tail)
end

mutual
/-- Term reduces (`⇛`) to its complete development [KS22, Proposition 3.7] -/
def term_to_development
  (t : Term)
  : t ⇛ complete_development t
  := match t with
    | loc n => by simp [complete_development]; exact prefl (loc n)
    | dot t a => by
        simp [complete_development]
        split
        · rename_i cd_is_obj
          rename_i l
          rename_i attrs
          split
          · rename_i lookup_attached
            rename_i u
            have goal := PReduce.pdot_c u a l (term_to_development t) cd_is_obj lookup_attached
            simp [cd_is_obj] at goal
            exact goal
          · have goal := PReduce.pcongDOT t (complete_development t) a (term_to_development t)
            simp [cd_is_obj] at goal
            exact goal
          · rename_i lookup_none
            exact dite ("φ" ∈ attrs)
              (fun φ_in => by
                simp [φ_in]
                have temp := term_to_development t
                simp [cd_is_obj] at temp
                exact PReduce.pdot_cφ a l temp rfl lookup_none φ_in
              )
              (fun not_in => by
                simp [not_in]
                have goal := PReduce.pcongDOT t (complete_development t) a (term_to_development t)
                simp [cd_is_obj] at goal
                exact goal
              )
        · rename_i cd_not_obj
          exact PReduce.pcongDOT t (complete_development t) a (term_to_development t)
    | app t a u => by
        simp [complete_development]
        split
        · rename_i cd_is_obj
          rename_i l
          split
          · rename_i lookup_void
            exact PReduce.papp_c
              a
              l
              (term_to_development t)
              (term_to_development u)
              cd_is_obj
              lookup_void
          · rename_i lookup_not_void
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
        · exact PReduce.pcongAPP
            t
            (complete_development t)
            u
            (complete_development u)
            a
            (term_to_development t)
            (term_to_development u)

    | obj bnds => by
        simp [complete_development]
        exact PReduce.pcongOBJ
          bnds
          (complete_developmentLst bnds)
          (term_to_development_Lst bnds)

def term_to_development_Lst
  { lst : List Attr}
  ( l : Bindings lst)
  : Premise l (complete_developmentLst l)
  := by match l with
  | Bindings.nil => simp ; exact Premise.nil
  | Bindings.cons _ _ void premise_tail =>
    simp
    apply Premise.consVoid
    exact term_to_development_Lst premise_tail
  | Bindings.cons _ _ (attached t) premise_tail =>
    simp
    apply Premise.consAttached
    · exact term_to_development t
    · exact term_to_development_Lst premise_tail
end

/-- Half Diamond [KS22, Proposition 3.8] -/
def half_diamond
  { t t' : Term }
  (preduce : PReduce t t')
  : PReduce t' (complete_development t)
  := match preduce with
    | .pcongOBJ l newAttrs premise => by
        simp [complete_development]
        let rec make_premise
          { lst : List Attr }
          { l l' : Bindings lst }
          (premise : Premise l l')
          : Premise l' (complete_developmentLst l)
          := match lst with
            | [] => match l, l' with
              | Bindings.nil, Bindings.nil => by simp; exact Premise.nil
            | a :: as => match premise with
              | Premise.consVoid _ premise_tail => by
                  simp [complete_development]
                  exact Premise.consVoid a (make_premise premise_tail)
              | Premise.consAttached _ t1 t2 preduce premise_tail => by
                  simp [complete_development]
                  exact Premise.consAttached
                    a
                    t2
                    (complete_development t1)
                    (half_diamond preduce)
                    (make_premise premise_tail)
        exact PReduce.pcongOBJ newAttrs (complete_developmentLst l) (make_premise premise)
    | .pcong_ρ n => by
        simp [complete_development]
        exact prefl (loc n)
    | .pcongDOT lt lt' a preduce => by
        simp [complete_development]
        split
        · rename_i cd_is_obj
          rename_i l
          rename_i attrs
          have assumption_preduce := half_diamond preduce
          simp [cd_is_obj] at assumption_preduce
          split
          · rename_i lookup_attached
            rename_i u
            exact PReduce.pdot_c u a l assumption_preduce rfl lookup_attached
          · exact PReduce.pcongDOT lt' (obj l) a assumption_preduce
          · rename_i lookup_none
            exact dite ("φ" ∈ attrs)
              (fun φ_in => by
                simp [φ_in]
                exact PReduce.pdot_cφ a l assumption_preduce rfl lookup_none φ_in
              )
              (fun not_in => by
                simp [not_in]
                exact PReduce.pcongDOT lt' (obj l) a assumption_preduce
              )
        · rename_i cd_not_obj
          exact PReduce.pcongDOT lt' (complete_development lt) a (half_diamond preduce)
    | .pcongAPP lt lt' lu lu' a preduce_lt preduce_lu => by
        simp [complete_development]
        split
        · rename_i cd_is_obj
          rename_i l
          rename_i attrs
          have assumption_preduce_lt := half_diamond preduce_lt
          have assumption_preduce_lu := half_diamond preduce_lu
          simp [cd_is_obj] at assumption_preduce_lt
          split
          · rename_i lookup_void
            exact PReduce.papp_c a l assumption_preduce_lt (assumption_preduce_lu) rfl lookup_void
          · rename_i lookup_void
            exact PReduce.pcongAPP lt' (obj l) lu' (complete_development lu) a
              assumption_preduce_lt assumption_preduce_lu
        · rename_i cd_not_obj
          exact PReduce.pcongAPP
            lt'
            (complete_development lt)
            lu'
            (complete_development lu)
            a
            (half_diamond preduce_lt)
            (half_diamond preduce_lu)
    | @PReduce.pdot_c lt lt' t_c c _ l preduce eq lookup_eq => by
        let pred
          : lt' ⇛ complete_development lt
          := half_diamond preduce
        generalize h : complete_development lt = foo
        simp [eq, h] at pred
        cases pred with
          | pcongOBJ l newAttrs premise =>
          simp [complete_development, h]
          let ⟨u, Pair.pair lookup_attached tc_to_u⟩ := lookup_attached_premise lookup_eq premise
          simp [lookup_attached, eq]
          let min_free_locs
            : le_nat_option_nat 0 (min_free_loc 0 (obj newAttrs))
            := by
              simp [le_nat_option_nat]
              split
              · exact Nat.zero_le _
              · simp
          exact substitution_lemma 0 tc_to_u (.pcongOBJ l newAttrs premise) min_free_locs

    | @PReduce.pdot_cφ lt lt' c lst l preduce eq lookup_none is_attr => by
        let pred
          : lt' ⇛ complete_development lt
          := half_diamond preduce
        generalize h : complete_development lt = foo
        simp [eq, h] at pred
        cases pred with
          | @pcongOBJ _ _ newAttrs premise =>
              simp [complete_development, h]
              let lookup_none
                := lookup_none_preserve lookup_none newAttrs
              simp [lookup_none, is_attr]
              let preduce := (PReduce.pcongOBJ _ _ premise)
              simp [<-eq] at preduce
              exact .pcongDOT _ _ c (.pcongDOT _ _ "φ" preduce)
    | @PReduce.papp_c lt lt' lu lu' c _ l preduce_t preduce_u eq lookup_eq => by
        let preduce_t' := half_diamond preduce_t
        let preduce_u' := half_diamond preduce_u
        generalize h : complete_development lt = foo
        simp [eq, h] at preduce_t'
        cases preduce_t' with
          | pcongOBJ _ newAttrs premise =>
              simp [complete_development, h]
              let lookup_void
                := lookup_void_premise lookup_eq premise
              simp [lookup_void]
              exact .pcongOBJ
                _
                _
                (singlePremiseInsert (preduce_incLocatorsFrom 0 preduce_u') premise)

/-! ### Confluence -/

/-- Diamond property of `⇛` [KS22, Corollary 3.9] -/

def diamond_preduce : DiamondProperty PReduce
  := fun t _ _ tu tv =>
    ⟨ complete_development t
    , (half_diamond tu)
    , (half_diamond tv)
    ⟩

/-- Confluence of `⇛` [KS22, Corollary 3.10], [Krivine93, Lemma 1.17] -/
def confluence_preduce : Confluence PReduce
  := diamond_implies_confluence diamond_preduce

/-- Confluence of `⇝` [KS22, Theorem 3.11] -/
def confluence_reduce : Confluence Reduce
  := fun t u v tu tv =>
  let (tu', tv') := (redMany_to_parMany tu, redMany_to_parMany tv)
  let ⟨w, uw', vw'⟩ := confluence_preduce t u v tu' tv'
  let (uw, vw) := (parMany_to_redMany uw', parMany_to_redMany vw')
  ⟨w, uw, vw⟩
