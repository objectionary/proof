-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Extended.Reduction.Parallel.Definition

set_option autoImplicit false

open PReduce
open Term

mutual

def prefl_ρ_premise
  {ctx : Ctx}
  {ρ : Option Term}
  : RhoPremise ctx ρ ρ
  := match ρ with
    | none => RhoPremise.none
    | some _ => RhoPremise.some prefl

def prefl_form_premise
  {ctx : Ctx}
  {attrs : Attrs}
  {bnds : Bindings attrs}
  : FormationPremise ctx bnds bnds
  := match attrs with
    | [] => match bnds with
      | Record.nil => FormationPremise.nil
    | _ :: _ => match bnds with
      | Record.cons _ _ none _ => FormationPremise.consVoid prefl_form_premise
      | Record.cons _ _ (some _) _ => FormationPremise.consAttached prefl prefl_form_premise

def prefl_app_premise
  {ctx : Ctx}
  {attrs : Attrs}
  {apps : Record Term attrs}
  : ApplicationPremise ctx apps apps
  := match attrs with
    | [] => match apps with
      | Record.nil => ApplicationPremise.nil
    | _ :: _ => match apps with
      | Record.cons _ _ _ _ => ApplicationPremise.cons prefl prefl_app_premise

def prefl
  {ctx : Ctx}
  {t : Term}
  : PReduce ctx t t
  := match t with
    | dot _ _ => pr_cong_dot prefl
    | app _ _ => pr_cong_app prefl_app_premise prefl
    | obj _ _ => pr_cong_obj prefl_ρ_premise prefl_form_premise
    | glob => pr_Φ_refl
    | this => pr_ξ_refl
    | termination => pr_termination_refl

end

namespace FormationPremise

def single
  {ctx : Ctx}
  {t t' : Term}
  {attrs : Attrs}
  (bnds : Bindings attrs)
  (attr : Attr)
  (pred : PReduce ctx t t')
  (contains : Contains bnds attr (some t))
  : FormationPremise ctx bnds (Record.insert bnds attr t')
  := match attrs with
    | [] => match bnds with | Record.nil => FormationPremise.nil
    | _ :: attrs_tail => match bnds with
      | Record.cons _ not_in none bnds_tail => match contains with
        | Contains.tail _ _ neq _ contains_tail => by
          simp [Record.insert, neq]
          exact FormationPremise.consVoid (single bnds_tail attr pred contains_tail)
      | Record.cons _ not_in (some term) bnds_tail => match contains with
        | Contains.head _ _ => by
          simp [Record.insert]
          exact FormationPremise.consAttached pred prefl_form_premise
        | Contains.tail _ _ neq _ contains_tail => by
          simp [Record.insert, neq]
          exact FormationPremise.consAttached prefl (single bnds_tail attr pred contains_tail)

end FormationPremise

namespace ApplicationPremise

def single
  {ctx : Ctx}
  {t t' : Term}
  {attrs : Attrs}
  (apps : Record Term attrs)
  (attr : Attr)
  (preduce : PReduce ctx t t')
  (contains : Contains apps attr t)
  : ApplicationPremise ctx apps (Record.insert apps attr t')
  := match attrs with
    | [] => match apps with | Record.nil => ApplicationPremise.nil
    | _ :: attrs_tail => match apps with
      | Record.cons _ not_in term bnds_tail => match contains with
        | Contains.head _ _ => by
          simp [Record.insert]
          exact ApplicationPremise.cons preduce prefl_app_premise
        | Contains.tail _ _ neq _ contains_tail => by
          simp [Record.insert, neq]
          exact ApplicationPremise.cons prefl (single bnds_tail attr preduce contains_tail)

end ApplicationPremise
