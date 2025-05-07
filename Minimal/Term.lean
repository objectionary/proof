-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Minimal.Record

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

/-! ### Defition of minimal φ-calculus terms -/

@[reducible]
def Attr := String


inductive Term : Type where
  | loc : Nat → Term                  -- ρⁿ
  | dot : Term → Attr → Term          -- t.α
  | app : Term → Attr → Term → Term   -- t(α ↦ u)
  | obj : { lst : List Attr } → Record (Option Term) lst → Term  -- ⟦ α → ... ⟧
open Term

@[simp, reducible]
def Bindings lst := Record (Option Term) lst

/-! ### Defition of increment, substitution, its properties, and auxiliary definitions that involve terms -/

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
    ( bnds : Bindings lst)
    : Bindings lst
    := match bnds with
    | .nil => .nil
    | .cons a not_in none tail =>
      .cons a not_in none (incLocatorsFromLst n tail)
    | .cons a not_in (some term) tail =>
      .cons a not_in (some (incLocatorsFrom n term)) (incLocatorsFromLst n tail)
end

def incLocators : Term → Term
  := incLocatorsFrom 0

mutual
/-- Locator substitution [KS22, Fig. 1] -/
  @[simp]
  def substitute : Nat × Term → Term → Term
  := λ (k, v) term => match term with
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
  := λ (k, v) o => match o with
  | .nil => .nil
  | .cons a not_in none tail =>
    .cons a not_in none (substituteLst (k, v) tail)
  | .cons a not_in (some term) tail =>
    .cons a not_in (some (substitute (k, v) term)) (substituteLst (k, v) tail)
end

instance : Min (Option Nat) where
  min
  | some k1, some k2 => some (min k1 k2)
  | some k, none => some k
  | none, some k => some k
  | none, none => none

/-- Minimal free locator in a term, if free locators exist, assuming free locators start at `zeroth_level`. -/
def min_free_loc
  (zeroth_level : Nat)
  : Term → Option Nat
  | loc k => if k < zeroth_level then none
    else some (k - zeroth_level)
  | dot t _ => min_free_loc zeroth_level t
  | app t _ u => min (min_free_loc zeroth_level t) (min_free_loc zeroth_level u)
  | obj o => match o with
    | .nil => none
    | .cons _ _ none tail => min_free_loc zeroth_level (obj tail)
    | .cons _ _ (some t) tail =>
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
    . constructor
      . assumption
      . apply Nat.le_trans le_min (by assumption)
    . constructor
      . exact Nat.le_of_lt (Nat.lt_of_le_of_lt le_min (Nat.gt_of_not_le (by assumption)))
      . assumption
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
    . exact le_and.left
    . exact le_and.right
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
    ( bindings : Bindings lst)
    ( free_locs : le_nat_option_nat i (min_free_loc j (obj bindings)))
    : le_nat_option_nat (i + 1) (min_free_loc j (obj (incLocatorsFromLst (j + 1) bindings)))
    := by match bindings with
      | .nil =>
        simp [min_free_loc, le_nat_option_nat]
      | .cons _ _ none tail =>
        simp [min_free_loc]
        exact traverse_bindings tail (by simp [min_free_loc] at free_locs ; exact free_locs)
      | .cons _ _ (some term) tail =>
        simp [min_free_loc]
        apply le_min_option_reverse
        constructor
        . simp [min_free_loc] at free_locs
          have free_locs := (le_min_option free_locs).left
          exact min_free_loc_inc free_locs
        . simp [min_free_loc] at free_locs
          have free_locs := le_min_option free_locs
          exact traverse_bindings tail free_locs.right
    exact traverse_bindings o free_locs_v


mutual
/-- `substitute` and `incLocatorsFrom` cancel effect of each other, if they act only on free locators. -/
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
    . rename_i n_is_not_free
      simp [Nat.lt_of_lt_of_le n_is_not_free le_0k]
      simp [substitute, Nat.lt_of_lt_of_le n_is_not_free le_0j]
    . rename_i n_is_free
      simp [le_nat_option_nat] at v_loc
      have n_is_free : zeroth_level ≤ n := Nat.ge_of_not_lt n_is_free
      have le_in: i + zeroth_level ≤ n :=
        (Nat.sub_add_cancel n_is_free) ▸ Nat.add_le_add_right v_loc zeroth_level
      have le_kn : k ≤ n := Nat.le_trans le_ki le_in
      have nlt_nk: ¬ n < k := λ x => Nat.lt_irrefl n (Nat.lt_of_lt_of_le x le_kn)
      simp [nlt_nk]
      have lt_jn1 : j < n + 1 := Nat.lt_succ_of_le (Nat.le_trans le_ji le_in)
      have nlt_n1j : ¬ n + 1 < j := λ x => Nat.lt_irrefl j (Nat.lt_trans lt_jn1 x)
      have neq_n1j : ¬ n + 1 = j := λ x => Nat.lt_irrefl j (x ▸ lt_jn1)
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
    . exact v_loc.left
    . exact v_loc.right
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
  | .nil => by simp
  | .cons _ _ none tail => by
    simp [min_free_loc] at *
    exact subst_inc_cancel_Lst tail u j k i zeroth_level le_ji le_ki le_0j le_0k v_loc
  | .cons _ _ (some term) tail => by
    simp
    constructor
    . simp [min_free_loc] at v_loc
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
    . simp [min_free_loc] at v_loc
      have free_locs := le_min_option v_loc
      exact subst_inc_cancel_Lst tail _ _ _ _ _ le_ji le_ki le_0j le_0k free_locs.right
end

def lookup { lst : List Attr } (l : Bindings lst) (a : Attr) : Option (Option Term)
  := match l with
    | .nil => none
    | .cons name _ opAttr tail =>
        if (name == a) then some opAttr
        else lookup tail a

theorem lookup_none_not_in
  { lst : List Attr }
  { l : Bindings lst }
  { a : Attr }
  (lookup_none : lookup l a = none)
  : a ∉ lst
  := λ a_in_lst => match lst with
    | [] => by contradiction
    | b :: bs => match l with
      | .cons _ _ opAttr tail =>
        dite
        (b = a)
        (λ eq => by simp [eq, lookup] at lookup_none)
        (λ neq => by
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
    | [] => match l2 with | .nil => by simp [lookup]
    | b :: bs => match l1, l2 with
      | .cons _ _ opAttr1 tail1, .cons _ _ opAttr2 tail2 => dite
        (b = a)
        (λ eq => by simp [lookup, eq] at lookup_none)
        (λ neq => by
          simp [lookup, neq] at lookup_none
          simp [lookup, neq]
          exact lookup_none_preserve lookup_none tail2
        )

def insert_φ
  { lst : List Attr }
  (l : Bindings lst)
  (a : Attr)
  (u : Option Term)
  : (Bindings lst)
  := match l with
    | .nil => .nil
    | .cons name not_in opAttr tail =>
        if name == a then .cons name not_in u tail
        else .cons name not_in opAttr (insert_φ tail a u)

inductive IsAttached : { lst : List Attr } → Attr → Term → Bindings lst → Type where
  | zeroth_attached
    : { lst : List Attr }
    → (a : Attr)
    → (not_in : a ∉ lst)
    → (t : Term)
    → (l : Bindings lst)
    → IsAttached a t (.cons a not_in (some t) l)
  | next_attached
    : { lst : List Attr }
    → (a : Attr)
    → (t : Term)
    → (l : Bindings lst)
    → (b : Attr)
    → (a ≠ b)
    → (not_in : b ∉ lst)
    → (u : Option Term)
    → IsAttached a t l
    → IsAttached a t (.cons b not_in u l)

theorem isAttachedIsIn
  { lst : List Attr }
  { a : Attr }
  { t : Term }
  { l : Bindings lst }
  : IsAttached a t l
  → a ∈ lst
  | @IsAttached.zeroth_attached lst' _a _ _t _ => List.Mem.head lst'
  | IsAttached.next_attached _ _ _ b _ _ _ isAttached' => List.Mem.tail b (isAttachedIsIn isAttached')

namespace Insert

  theorem insertAttachedStep
    { a b : Attr }
    { neq : a ≠ b }
    { t : Term }
    { lst : List Attr }
    { not_in : b ∉ lst }
    { u : Option Term }
    { l : Bindings lst }
    : insert_φ (.cons b not_in u l) a (some t)
        = .cons b not_in u (insert_φ l a (some t))
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
    → insert_φ l a (some t) = l
      | IsAttached.zeroth_attached _ _ _ _ => by simp [insert_φ]
      | IsAttached.next_attached _ _ l b neq not_in u isAttached =>
          let step := @insertAttachedStep a b neq t _ not_in u _
          Eq.trans step (congrArg (Record.cons b not_in u) (insertAttached isAttached))

  theorem insertTwice
    {lst : List Attr}
    (l : Bindings lst)
    (a : Attr)
    (t t' : Term)
    : insert_φ (insert_φ l a (some t')) a (some t) = insert_φ l a (some t)
    := match lst with
      | [] => match l with
        | .nil => by simp [insert_φ]
      | b :: bs => match l with
        | .cons _ not_in _ tail => dite (a = b)
          (λ eq => by simp [insert_φ, eq])
          (λ neq =>
            let neq' : b ≠ a := λ eq => neq eq.symm
            by  simp [insert_φ, neq']
                exact insertTwice tail a t t'
          )

  def insert_new_isAttached
    { lst : List Attr }
    { l : Bindings lst }
    { a : Attr }
    { t t' : Term}
    : IsAttached a t l → IsAttached a t' (insert_φ l a (some t'))
    := λ isAttached => match isAttached with
      | IsAttached.zeroth_attached _ not_in _ _=> by
        simp [insert_φ]
        exact IsAttached.zeroth_attached _ _ _ _
      | IsAttached.next_attached _ _ l b neq not_in u new_isAttached => by
        have hypothesis : IsAttached a t' (insert_φ l a (some t'))
          := insert_new_isAttached new_isAttached
        simp [insert_φ, neq.symm]
        exact IsAttached.next_attached a t' (insert_φ l a (some t')) b neq not_in u hypothesis

end Insert


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
      simp
      exact inc_swap i j le_ij s
    | app s a u => by
      simp
      constructor
      . exact inc_swap i j le_ij s
      . exact inc_swap i j le_ij u
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
  | .nil => by simp
  | .cons _ _ none tail => by
    simp
    exact inc_swap_Lst i j le_ij tail
  | .cons _ _ (some t) tail => by
    simp
    constructor
    . exact inc_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ij) t
    . exact inc_swap_Lst i j le_ij tail
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
  | .nil => simp
  | .cons _ _ none tail =>
    simp
    exact subst_inc_swap_Lst i j le_ji tail u
  | .cons _ _ (some t) tail =>
    simp
    constructor
    . simp [incLocators, inc_swap]
      rw [← incLocators]
      exact subst_inc_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ji) t (incLocators u)
    . exact subst_inc_swap_Lst i j le_ji tail u
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
      . rename_i lt_kj
        have lt_ki: k < i := Nat.lt_of_lt_of_le lt_kj le_ji
        have lt_ki1 : k < i + 1 := Nat.lt_succ_of_le (Nat.le_of_lt lt_ki)
        simp [lt_ki1, lt_ki, lt_kj]
      . rename_i nlt_kj
        split
        . rename_i eq_kj
          simp [eq_kj, Nat.lt_succ_of_le le_ji]
        . rename_i neq_kj
          have lt_jk : j < k := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt nlt_kj) (λ x => neq_kj x.symm)
          have le_k1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
          have k0 : k - 1 + 1 = k := Nat.sub_add_cancel le_k1
          split
          . rename_i lt_ki1
            have lt_k1i : k - 1 < i := Nat.lt_of_succ_lt_succ (k0.symm ▸ lt_ki1)
            simp [nlt_kj, neq_kj, lt_k1i]
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
            simp [nlt_k1i, neq_k1j, nlt_k1j, k0, Nat.add_sub_cancel]
    | dot s a => by
      simp
      exact inc_subst_swap i j le_ji s u
    | app s₁ a s₂ => by
      simp
      constructor
      . exact inc_subst_swap i j le_ji s₁ u
      . exact inc_subst_swap i j le_ji s₂ u
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
  | .nil => simp
  | .cons _ _ none tail =>
    simp
    exact inc_subst_swap_Lst i j le_ji tail u
  | .cons _ _ (some t) tail =>
    simp
    constructor
    . simp [incLocators, inc_swap]
      rw [← incLocators]
      exact inc_subst_swap (i + 1) (j + 1) (Nat.succ_le_succ le_ji) t (incLocators u)
    . exact inc_subst_swap_Lst i j le_ji tail u
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
        . rename_i lt_kj
          have lt_ki : k < i := Nat.le_trans lt_kj le_ji
          have lt_ki1 : k < i + 1 := Nat.le_step lt_ki
          simp [lt_kj, lt_ki, lt_ki1]
          -- case k < j
        . rename_i not_lt
          have le_jk: j ≤ k := Nat.ge_of_not_lt not_lt
          split
          . rename_i eq_kj
            have lt_ji1 : j < i + 1 :=  Nat.lt_succ_of_le le_ji
            simp [eq_kj, lt_ji1]
            -- case k == j
          . rename_i neq_kj
            have neq_jk : ¬j = k := λ eq => neq_kj eq.symm
            have lt_jk : j < k := Nat.lt_of_le_of_ne le_jk neq_jk
            simp
            have le_k1: 1 ≤ k := Nat.succ_le_of_lt
              (Nat.lt_of_le_of_lt (Nat.zero_le j) lt_jk)
            split
            . rename_i le_k1i
              have lt_ki1: k < i + 1 := by
                have temp := Nat.add_lt_add_right le_k1i 1
                simp [Nat.sub_add_cancel le_k1] at temp
                exact temp
              have nlt_kj : ¬ k < j := λ lt_kj => Nat.lt_irrefl k (Nat.lt_trans lt_kj lt_jk)
              simp [lt_ki1, neq_kj, nlt_kj]
              -- case j < k ≤ i
            . rename_i nlt_k1i
              split
              . rename_i eq_k1i
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
              . rename_i neq_k1i
                have lt_ik1: i < k - 1 := Nat.lt_of_le_of_ne (Nat.ge_of_not_lt (nlt_k1i)) (λ x => neq_k1i x.symm)
                have lt_i1k : i + 1 < k := by
                  have := Nat.add_lt_add_right lt_ik1 1
                  simp [Nat.sub_add_cancel le_k1] at this
                  exact this
                have nle_ki1 : ¬ k < i + 1 := λ x => Nat.lt_irrefl k (Nat.lt_trans x lt_i1k)
                have neq_ki1 : ¬ k = i + 1 := λ x => Nat.lt_irrefl k (x ▸ lt_i1k)
                simp [nle_ki1, neq_ki1]
                have nlt_k1j : ¬ k - 1 < j := λ x => Nat.lt_irrefl j
                  (Nat.lt_trans (Nat.lt_of_le_of_lt le_ji lt_ik1) x)
                have neq : ¬ k - 1 = j := λ x => Nat.lt_irrefl j
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
  substituteLst (j + 1, incLocators (substitute (i, v) u)) (substituteLst (i + 1 + 1, incLocators (incLocators v)) o)
  := by match o with
  | .nil => simp
  | .cons _ _ none tail =>
    simp
    exact subst_swap_Lst i j le_ji tail u v free_locs_v
  | .cons _ _ (some t) tail =>
    simp
    constructor
    . simp [incLocators]
      simp [← subst_inc_swap]
      rw [← incLocators]
      exact subst_swap (i+1) (j+1) (Nat.add_le_add_right le_ji 1) t (incLocators u) (incLocators v) (min_free_loc_inc free_locs_v)
    . exact subst_swap_Lst i j le_ji tail u v free_locs_v
end

theorem lookup_inc_attached
  (t : Term)
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some (some t))
  : lookup (incLocatorsFromLst i l) c = some (some (incLocatorsFrom i t))
  := by match l with
  | .nil => contradiction
  | .cons name _ none tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . simp at lookup_eq
    . rename_i neq
      simp [lookup, neq]
      exact (lookup_inc_attached t i c tail lookup_eq)
  | .cons name _ (some _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . rename_i eq
      simp at lookup_eq
      simp [lookup_eq]
      simp [lookup_eq, lookup, eq]
    . rename_i neq
      simp [lookup, neq]
      exact (lookup_inc_attached t i c tail lookup_eq)

theorem lookup_inc_void
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some none)
  : lookup (incLocatorsFromLst i l) c = some none
  := by match l with
  | .nil => contradiction
  | .cons name _ none tail =>
    simp [lookup] at lookup_eq
    exact (dite (name = c)
      (λ lookup_eq => by
        simp [lookup, lookup_eq]))
      (λ neq => by
        simp [lookup, neq]
        exact (lookup_inc_void i c tail (lookup_eq neq)))
  | .cons name _ (some _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . simp at lookup_eq
    . rename_i neq
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
  | .nil => simp ; assumption
  | .cons name _ u tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . contradiction
    . rename_i neq
      cases u
      repeat simp [lookup, neq] ; exact (lookup_inc_none i c tail lookup_eq)

theorem inc_insert
  { i : Nat }
  { c : Attr }
  { lst : List Attr }
  { l : Bindings lst }
  { v : Term}
  : (insert_φ (incLocatorsFromLst (i + 1) l) c (some (incLocators (incLocatorsFrom i v)))) =
  (incLocatorsFromLst (i + 1) (insert_φ l c (some (incLocators v))))
  := match l with
  | .nil => by
    simp [insert_φ]
  | .cons a not_in u _tail => by
    cases u
    repeat
      simp [insert_φ]
      split
      . simp
        rw [incLocators]
        simp [inc_swap]
      . simp
        apply inc_insert

theorem lookup_subst_attached
  (t : Term)
  {u : Term}
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some (some t))
  : lookup (substituteLst (i, u) l) c = some (some (substitute (i, u) t))
  := by match l with
  | .nil => contradiction
  | .cons name _ none tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . simp at lookup_eq
    . rename_i neq
      simp [lookup, neq]
      exact (lookup_subst_attached t i c tail lookup_eq)
  | .cons name _ (some _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . rename_i eq
      simp at lookup_eq
      simp [lookup_eq]
      simp [lookup_eq, lookup, eq]
    . rename_i neq
      simp [lookup, neq]
      exact (lookup_subst_attached t i c tail lookup_eq)

theorem lookup_subst_void
  {u : Term}
  (i : Nat)
  (c : Attr)
  {lst : List Attr}
  (l : Bindings lst)
  (lookup_eq: lookup l c = some none)
  : lookup (substituteLst (i, u) l) c = some none
  := by match l with
  | .nil => contradiction
  | .cons name _ none tail =>
    simp [lookup] at lookup_eq
    exact (dite (name = c)
      (λ lookup_eq => by
        simp [lookup, lookup_eq]))
      (λ neq => by
        simp [lookup, neq]
        exact (lookup_subst_void i c tail (lookup_eq neq)))
  | .cons name _ (some _) tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . simp at lookup_eq
    . rename_i neq
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
  | .nil => simp ; assumption
  | .cons name _ u tail =>
    simp [lookup] at lookup_eq
    split at lookup_eq
    . contradiction
    . rename_i neq
      cases u
      repeat simp [lookup, neq] ; exact (lookup_subst_none i c tail lookup_eq)

theorem subst_insert
  { i : Nat }
  { c : Attr }
  { lst : List Attr }
  { l : Bindings lst }
  { u v : Term}
  : (insert_φ (substituteLst (i + 1, incLocators u) l) c (some (incLocators (substitute (i, u) v))))
  = (substituteLst (i + 1, incLocators u) (insert_φ l c (some (incLocators v))))
  := match l with
  | .nil => by
    simp [insert_φ]
  | .cons a not_in u _tail => by
    cases u
    repeat
      simp [insert_φ]
      split
      . simp
        rw [incLocators]
        simp [subst_inc_swap]
      . simp
        apply subst_insert
