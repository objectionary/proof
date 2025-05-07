-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Minimal.Term
import Minimal.Reduction.Parallel.Definition

open Term

set_option autoImplicit false

/-! ### Auxilary properties of parallel reduction -/

mutual
  def reflexivePremise
    { lst : List Attr }
    (l : Bindings lst)
    : Premise l l
    := match l with
      | .nil => Premise.nil
      | .cons name not_in opAttr tail =>
          match opAttr with
            | none => Premise.consVoid name (reflexivePremise tail)
            | some t => Premise.consAttached name t t (prefl t) (reflexivePremise tail)

/-- Reflexivity of parallel reduction [KS22, Proposition 3.3] -/
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
  (l : Bindings lst)
  (a : Attr)
  (t : Term)
  (t' : Term)
  (isAttached : IsAttached a t l)
  (preduce : PReduce t t')
  : Premise l (insert_φ l a (some t'))
  := match lst with
    | [] => match l with
      | .nil => Premise.nil
    | b :: bs => match isAttached with
      | IsAttached.zeroth_attached _ _ _ tail => match l with
        | .cons _ _ _ _ => by
            simp [insert_φ]
            exact Premise.consAttached b t t' preduce (reflexivePremise tail)
      | IsAttached.next_attached _ _ tail _ neq not_in u newIsAttached => match l with
        | .cons _ _ _ _ => by
            have neq' : b ≠ a := λ eq => neq eq.symm
            simp [insert_φ, neq']
            have premise := (singlePremise tail a t t' newIsAttached preduce)
            exact (match u with
              | none => Premise.consVoid b premise
              | some u' => Premise.consAttached b u' u' (prefl u') premise
            )

def singlePremiseInsert
  { lst : List Attr }
  { l1 l2 : Bindings lst }
  { a : Attr }
  { t1 t2 : Term }
  (preduce : PReduce t1 t2)
  (premise : Premise l1 l2)
  : Premise (insert_φ l1 a (some t1)) (insert_φ l2 a (some t2))
  := match premise with
    | Premise.nil => Premise.nil
    | Premise.consVoid b tail => dite
        (b = a)
        (λ eq => by
          simp [insert_φ, eq]
          exact Premise.consAttached b _ _ preduce tail
        )
        (λ neq => by
          simp [insert_φ, neq]
          exact Premise.consVoid b (singlePremiseInsert preduce tail)
        )
    | Premise.consAttached b t' t'' preduce' tail => dite
        (b = a)
        (λ eq => by
          simp [insert_φ, eq]
          exact Premise.consAttached b _ _ preduce tail
        )
        (λ neq => by
          simp [insert_φ, neq]
          exact Premise.consAttached b t' t'' preduce' (singlePremiseInsert preduce tail)
        )

theorem lookup_void_premise
  { lst : List Attr }
  { l1 l2 : Bindings lst }
  { a : Attr }
  (lookup_void : lookup l1 a = some none)
  (premise : Premise l1 l2)
  : lookup l2 a = some none
  := match lst with
    | [] => match l1, l2 with | .nil, .nil => by contradiction
    | b :: bs => match l1, l2 with
        | .cons _ _ _ tail1, .cons _ _ _ tail2 => match premise with
          | Premise.consVoid _ premise_tail => dite
            (b = a)
            (λ eq => by simp [lookup, eq])
            (λ neq => by
              simp [lookup, neq] at lookup_void
              simp [lookup, neq]
              exact lookup_void_premise lookup_void premise_tail
            )
          | Premise.consAttached _ _ _ _ premise_tail => dite
            (b = a)
            (λ eq => by simp [lookup, eq] at lookup_void)
            (λ neq => by
              simp [lookup, neq] at lookup_void
              simp [lookup, neq]
              exact lookup_void_premise lookup_void premise_tail
            )

def lookup_attached_premise
  { lst : List Attr }
  { l1 l2 : Bindings lst }
  { a : Attr }
  { u : Term }
  (lookup_attached : lookup l1 a = some (some u))
  (premise : Premise l1 l2)
  : Σ u' : Term, PProd (lookup l2 a = some (some u')) (PReduce u u')
  := match lst with
    | [] => match l1, l2 with | .nil, .nil => match premise with
      | Premise.nil => by
        simp [lookup]
        contradiction
    | b :: bs => match premise with
      | Premise.consVoid _ premise_tail => by
        simp [lookup]
        exact dite
          (b = a)
          (λ eq => by
            simp [lookup, eq] at lookup_attached
          )
          (λ neq => by
            simp [lookup, neq]
            simp [lookup, neq] at lookup_attached
            exact lookup_attached_premise (lookup_attached) premise_tail
          )
      | Premise.consAttached _ t1 t2 preduce premise_tail => by
        simp [lookup]
        exact dite
          (b = a)
          (λ eq => by
            simp [eq]
            simp [lookup, eq] at lookup_attached
            simp [lookup_attached] at preduce
            exact ⟨t2, PProd.mk rfl preduce⟩
          )
          (λ neq => by
            simp [neq]
            simp [lookup, neq] at lookup_attached
            exact lookup_attached_premise (lookup_attached) premise_tail
          )

mutual
/-- Increment of locators preserves parallel reduction. -/
def preduce_incLocatorsFrom
  { t t' : Term}
  ( i : Nat)
  : ( t ⇛ t') → (incLocatorsFrom i t ⇛ incLocatorsFrom i t')
  | .pcongOBJ bnds bnds' premise => by
    simp
    exact PReduce.pcongOBJ (incLocatorsFromLst (i + 1) bnds) (incLocatorsFromLst (i + 1) bnds') (preduce_incLocatorsFrom_Lst i premise)
  | .pcong_ρ n =>  prefl (incLocatorsFrom i (loc n))
  | .pcongAPP t t' u u' a tt' uu' => by
    simp
    apply PReduce.pcongAPP
    . exact preduce_incLocatorsFrom i tt'
    . exact preduce_incLocatorsFrom i uu'
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
    | .nil, .nil => by
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
