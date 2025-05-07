-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Minimal.Term
import Minimal.Reduction.Parallel.AuxilaryProperties
import Minimal.Reduction.Parallel.Definition

open Term

set_option autoImplicit false

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
      (substituteLst (i + 1, incLocators u) bnds) (substituteLst (i + 1, incLocators u') bnds') (substitution_lemma_Lst i premise uu' min_free_locs_u')
  | .pcong_ρ n => by
    simp
    exact dite (n < i)
      (λ less => by
        simp [less]
        exact PReduce.pcong_ρ n
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
    have : substitute (0, substitute (i, u') s') (substitute (i + 1, incLocators u') t_c) = substitute (i, u') (substitute (0, s') t_c) := (subst_swap i 0 (Nat.zero_le i) t_c s' u' ((by assumption))).symm
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
    . apply substitution_lemma
      exact preduce
      exact preduce_incLocatorsFrom 0 uu'
      exact min_free_loc_inc min_free_locs_u
    . exact substitution_lemma_Lst i premise_tail uu' min_free_locs_u
end
