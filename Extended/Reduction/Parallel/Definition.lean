-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Extended.Term
import  Extended.Reduction.Regular.Definition

set_option autoImplicit false

/-! ### Defition of φ-calculus parallel term reduction `⇛` -/

open Term

mutual

-- | tᵢ ⇛ tᵢ' for all i with ⟦ ... αᵢ ↦ tᵢ ... ⟧
--   α's are given by `attrs`
inductive FormationPremise : {attrs : Attrs} → Ctx → Bindings attrs → Bindings attrs → Type where
  | nil : {ctx : Ctx} → FormationPremise ctx .nil .nil
  | consVoid
    : { ctx : Ctx }
    → { attr : Attr }
    → { attrs : Attrs }
    → { bnds1 : Bindings attrs }
    → { bnds2 : Bindings attrs }
    → { not_in : attr ∉ attrs }
    → FormationPremise ctx bnds1 bnds2
    → FormationPremise ctx (.cons attr not_in none bnds1) (.cons attr not_in none bnds2)
  | consAttached
    : { ctx : Ctx }
    → { attr : Attr }
    → { t1 : Term }
    → { t2 : Term }
    → PReduce ctx t1 t2
    → { attrs : Attrs }
    → { bnds1 : Bindings attrs }
    → { bnds2 : Bindings attrs }
    → { not_in : attr ∉ attrs }
    → FormationPremise ctx bnds1 bnds2
    → FormationPremise ctx (.cons attr not_in (some t1) bnds1) (.cons attr not_in (some t2) bnds2)

inductive RhoPremise : Ctx → Option Term → Option Term → Type where
  | none : {ctx : Ctx} → RhoPremise ctx none none
  | some
    : {ctx : Ctx}
    → {t t' : Term}
    → PReduce ctx t t'
    → RhoPremise ctx (some t) (some t')

inductive ApplicationPremise : {attrs : Attrs} → Ctx → Record Term attrs → Record Term attrs → Type where
  | nil : {ctx : Ctx} → ApplicationPremise ctx .nil .nil
  | cons
    : { ctx : Ctx }
    → { attr : Attr }
    → { t1 : Term }
    → { t2 : Term }
    → PReduce ctx t1 t2
    → { attrs : Attrs }
    → { apps1 : Record Term attrs }
    → { apps2 : Record Term attrs }
    → { not_in : attr ∉ attrs }
    → ApplicationPremise ctx apps1 apps2
    → ApplicationPremise ctx (.cons attr not_in t1 apps1) (.cons attr not_in t2 apps2)


inductive PReduce : Ctx → Term → Term → Type where
  -- Dispatch
  | pr_dot
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → { t t_inner : Term }
    → PReduce ctx t (obj ρ bnds)
    → lookup ρ bnds attr = LookupRes.attached t_inner
    → PReduce ctx (dot t attr) (substitute t_inner (obj ρ bnds))
  | pr_φ
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → { t : Term }
    → PReduce ctx t (obj ρ bnds)
    → lookup ρ bnds attr = LookupRes.absent
    → "φ" ∈ attrs
    → PReduce ctx (dot t attr) (dot (dot (obj ρ bnds) "φ") attr)
  | pr_stop
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → { t : Term }
    → PReduce ctx t (obj ρ bnds)
    → lookup ρ bnds attr = LookupRes.absent
    → lookup ρ bnds "φ" = LookupRes.absent
    → lookup ρ bnds "λ" = LookupRes.absent
    → PReduce ctx (dot t attr) termination
  -- Application
  | pr_empty
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { t : Term }
    → PReduce ctx t (obj ρ bnds)
    → PReduce ctx (app t Record.nil) (obj ρ bnds)
  -- | pr_copy
  --   : { ρ : Option Term }
  --   → { attrs app_attrs : Attrs }
  --   → { bnds : Bindings attrs }
  --   → { app_record_tail : Record Term app_attrs }
  --   → { attr : Attr }
  --   → { not_in : attr ∉ app_attrs }
  --   → { g s t u u' : Term }
  --   → PReduce {glob := g, scope := s} t (obj ρ bnds)
  --   → PReduce {glob := g, scope := s} u u'
  --   → lookup ρ bnds attr = LookupRes.void
  --   → PReduce
  --       { glob := g, scope := s }
  --       (app t (Record.cons attr not_in u app_record_tail))
  --       (app (insert ρ bnds attr (substitute u' s)) app_record_tail)
  | pr_over
    : { ρ : Option Term }
    → { attrs app_attrs : Attrs }
    → { bnds : Bindings attrs }
    → { app_record_tail : Record Term app_attrs }
    → { attr : Attr }
    → { not_in : attr ∉ app_attrs }
    → { ctx : Ctx }
    → { t t_inner u : Term }
    → PReduce ctx t (obj ρ bnds)
    → lookup ρ bnds attr = LookupRes.attached t_inner
    → PReduce
        ctx
        (app t (Record.cons attr not_in u app_record_tail))
        termination
  | pr_miss
    : { ρ : Option Term }
    → { attrs app_attrs : Attrs }
    → { bnds : Bindings attrs }
    → { app_record_tail : Record Term app_attrs }
    → { attr : Attr }
    → { not_in : attr ∉ app_attrs }
    → { ctx : Ctx }
    → { t u : Term }
    → PReduce ctx t (obj ρ bnds)
    → lookup ρ bnds attr = LookupRes.absent
    → lookup ρ bnds "φ" = LookupRes.absent
    → lookup ρ bnds "λ" = LookupRes.absent
    → PReduce
        ctx
        (app t (Record.cons attr not_in u app_record_tail))
        termination
  -- Special terms
  | pr_Φ
    : { g s : Term}
    → PReduce { glob := g, scope := s} glob g
  | pr_dd
    : { ctx : Ctx }
    → { attr : Attr }
    → PReduce ctx (dot termination attr) termination
  | pr_dc
    : { app_attrs : Attrs }
    → { record : Record Term app_attrs }
    → { ctx : Ctx }
    → PReduce ctx (app termination record) termination
  -- Congruence
  | pr_cong_app
    : { ctx : Ctx }
    → {t t' : Term}
    → {app_attrs : Attrs}
    → {apps new_apps : Record Term app_attrs}
    → ApplicationPremise ctx apps new_apps
    → PReduce ctx t t'
    → PReduce
        ctx
        (app t apps)
        (app t' new_apps)
  | pr_cong_dot
    : { ctx : Ctx }
    → {t t' : Term}
    → {attr : Attr}
    → PReduce ctx t t'
    → PReduce ctx (dot t attr) (dot t' attr)
  | pr_cong_obj
    : {ctx : Ctx}
    → {ρ ρ' : Option Term}
    → {attrs : Attrs}
    → {bnds new_bnds : Bindings attrs}
    → RhoPremise ctx ρ ρ'
    → FormationPremise ctx bnds new_bnds
    → PReduce
        ctx
        (obj ρ bnds)
        (obj ρ' new_bnds)
  -- Reflexive
  | pr_termination_refl
    : { ctx : Ctx }
    → PReduce ctx termination termination
  | pr_ξ_refl
    : { ctx : Ctx }
    → PReduce ctx this this
  | pr_Φ_refl
    : { ctx : Ctx }
    → PReduce ctx glob glob

end

def PReducesTo (t t' : Term) := PReduce {glob := t, scope := t} t t'
def PReducesToMany := ReflTransGen PReducesTo

infix:20 " ⇛ " => PReducesTo
infix:20 " ⇛* " => PReducesToMany

def get_form_premise
  {attrs : List Attr}
  {ρ : Option Term}
  {bnds bnds' : Bindings attrs}
  {ctx : Ctx}
  (preduce : PReduce ctx (obj ρ bnds) (obj ρ bnds'))
  : FormationPremise ctx bnds bnds'
  := match preduce with
    | .pr_cong_obj _ premise => premise

def get_ρ_premise
  {attrs : List Attr}
  {ρ : Option Term}
  {bnds bnds' : Bindings attrs}
  {ctx : Ctx}
  (preduce : PReduce ctx (obj ρ bnds) (obj ρ bnds'))
  : Σ ρ' : Option Term, RhoPremise ctx ρ ρ'
  := match preduce with
    | .pr_cong_obj premise _ => ⟨_, premise⟩

def get_application_premise
  {attrs : List Attr}
  {t : Term}
  {apps apps' : Record Term attrs}
  {ctx : Ctx}
  (preduce : PReduce ctx (app t apps) (app t apps'))
  : ApplicationPremise ctx apps apps'
  := match preduce with
    | .pr_cong_app premise _ => premise
