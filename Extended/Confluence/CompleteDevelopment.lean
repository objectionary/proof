import Extended.Term
import Extended.Reduction.Parallel.Definition
import Extended.Reduction.Parallel.Properties
import Minimal.Utils

open Term

set_option autoImplicit false

mutual
@[simp]
def complete_development : Ctx → Term → Term
  := λ ctx term => match term with
  | dot t a => match (complete_development ctx t) with
    | @obj attrs ρ bnds => match (lookup ρ bnds a) with
      | .attached t_a => (substitute t_a (obj ρ bnds))
      | .void => dot (obj ρ bnds) a
      | .absent => if ("φ" ∈ attrs) then dot (dot (obj ρ bnds) "φ") a else
          if ("λ" ∈ attrs) then dot (obj ρ bnds) a else termination
    | termination => termination
    | t' => dot t' a
  | app t apps => match (complete_development ctx t) with
    | @obj attrs ρ bnds => match apps with
      | .nil => obj ρ bnds
      | .cons a _ _ _ => match (lookup ρ bnds a) with
        | .void => app (obj ρ bnds) (complete_development_apps ctx apps)--(insert_φ bnds a (some (incLocators (complete_development u))))
        | .attached _ => termination
        | .absent => if "φ" ∉ attrs ∧ "λ" ∉ attrs then termination else app (obj ρ bnds) (complete_development_apps ctx apps)
    | termination => termination
    | _ => app (complete_development ctx t) (complete_development_apps ctx apps)
  | obj none bnds => obj none (complete_development_bnds ctx bnds)
  | obj (some ρ) bnds => obj (some (complete_development ctx ρ)) (complete_development_bnds ctx bnds)
  | glob => ctx.glob
  | this => this
  | termination => termination
@[simp]
def complete_development_bnds {attrs : Attrs} (ctx : Ctx) : Bindings attrs → Bindings attrs
  | .nil => .nil
  | .cons attr not_in none tail => .cons attr not_in none (complete_development_bnds ctx tail)
  | .cons attr not_in (some t) tail => .cons attr not_in (some (complete_development ctx t)) (complete_development_bnds ctx tail)
@[simp]
def complete_development_apps {attrs : Attrs} (ctx : Ctx) : Record Term attrs → Record Term attrs
  | .nil => .nil
  | .cons attr not_in u tail => .cons attr not_in (complete_development ctx u) (complete_development_apps ctx tail)
end

@[simp]
theorem termination_after_substitution
  {t : Term}
  {attrs : Attrs}
  {bnds : Bindings attrs}
  {ρ : Option Term}
  (_eq : substitute t (obj ρ bnds) = termination)
  : termination = t
  := match t with
  | dot term attr => by contradiction
  | app term apps => by contradiction
  | obj none bnds => by contradiction
  | obj (some term) bnds => by contradiction
  | this => by contradiction
  | glob => by contradiction
  | termination => rfl

mutual
-- def pred_to_obj_means_cd_obj
--   {ctx : Ctx}
--   {t : Term}
--   {ρ : Option Term}
--   {attrs : Attrs}
--   {bnds : Bindings attrs}
--   (preduce : PReduce ctx t (obj ρ bnds))
--   : ∃ new_ρ
--   , ∃ (new_bnds : Bindings attrs)
--   , complete_development ctx t = obj new_ρ new_bnds
--   := by
--     have preduce' := half_diamond preduce
--     generalize h : complete_development ctx t = foo
--     simp [h] at preduce'
--     match preduce' with
--     | .pr_cong_obj ρ_premise premise =>
--       rename_i new_bnds
--       rename_i new_ρ
--       exact ⟨new_ρ, new_bnds, rfl⟩

def pred_to_obj_means_cd_obj
  {ctx : Ctx}
  {t : Term}
  {ρ : Option Term}
  {attrs : Attrs}
  {bnds : Bindings attrs}
  (preduce : PReduce ctx t (obj ρ bnds))
  : (new_ρ : Option Term)
  ×' (new_bnds : Bindings attrs)
  ×' complete_development ctx t = obj new_ρ new_bnds
  := by
    have preduce' := half_diamond preduce
    generalize h : complete_development ctx t = foo
    simp [h] at preduce'
    match preduce' with
    | .pr_cong_obj ρ_premise premise =>
      rename_i new_bnds
      rename_i new_ρ
      exact ⟨new_ρ, new_bnds, rfl⟩
-- def cd_obj_keeps_void
--   {ctx : Ctx}
--   {t : Term}
--   {ρ : Option Term}
--   {attrs : Attrs}
--   {attr : Attr}
--   {bnds : Bindings attrs}
--   (preduce : PReduce ctx t (obj ρ bnds))
--   (attr_void : lookup ρ bnds attr = .void)
--   : ∃ new_ρ
--   , ∃ (new_bnds : Bindings attrs)
--   , complete_development ctx t = obj new_ρ new_bnds
--   ∧ lookup new_ρ new_bnds attr = .void
--   := by
--     have preduce' := half_diamond preduce
--     generalize h : complete_development ctx t = foo
--     simp [h] at preduce'
--     match preduce' with
--     | .pr_cong_obj ρ_premise premise =>
--       rename_i new_bnds
--       rename_i new_ρ
--       -- exact ⟨new_ρ, new_bnds, rfl⟩
--       admit

def pred_to_termination_means_cd_termination
  {ctx : Ctx}
  {t : Term}
  (preduce : PReduce ctx t termination)
  : complete_development ctx t = termination
  := match t with
  | termination => rfl
  | this => by contradiction
  | glob => by
    simp
    match ctx with
    | { glob := termination, scope := _ } => rfl
  | obj ρ bnds => by contradiction
  | app term apps => match preduce with
    | .pr_over pred attr_attached => by
      have ⟨_, _, h⟩ := pred_to_obj_means_cd_obj pred
      simp [h]
      admit
    | .pr_miss _ _ _ _ => sorry
    | .pr_dc => by simp
  | dot t attr => by
    simp
    generalize h : termination = foo
    simp [h] at preduce
    match preduce with
    | .pr_dot _ _ => exact sorry
    | .pr_stop _ _ _ _ => exact sorry
    | .pr_dd => exact sorry

-- def new_ρ_premise
--   {ctx : Ctx}
--   {ρ ρ' : Option Term}
--   (ρ_premise : RhoPremise ctx ρ ρ')
--   : Σ new_ρ, RhoPremise ctx ρ' new_ρ
--   := match ρ_premise with
--   | .none => ⟨none, .none⟩
--   | .some preduce =>
--     let h := half_diamond preduce
--     ⟨_, .some h⟩

def new_form_premise
  {ctx : Ctx}
  {attrs : Attrs}
  {bnds bnds' : Bindings attrs}
  (premise : FormationPremise ctx bnds bnds')
  : FormationPremise ctx bnds' (complete_development_bnds ctx bnds)
  := match attrs with
  | [] => match bnds, bnds' with | .nil, .nil => .nil
  | a :: as => match premise with
    | .consVoid premise_tail => .consVoid (new_form_premise premise_tail)
    | .consAttached preduce premise_tail =>
      let h_premise := new_form_premise premise_tail
      let h_preduce := half_diamond preduce
      .consAttached h_preduce h_premise

def half_diamond
  {ctx : Ctx}
  {t t' : Term}
  (preduce : PReduce ctx t t')
  : PReduce ctx t' (complete_development ctx t)
  := match preduce with
  | .pr_dot pred attr_attached => _ --by
    -- simp [complete_development]
    -- exact _
  | .pr_φ pred attr_absent φ_in => _
  | .pr_stop pred attr_absent φ_absent lam_absent => _
  | .pr_empty pred => by
    have ⟨new_ρ, new_bnds, cd_is_obj⟩ := pred_to_obj_means_cd_obj pred
    simp [cd_is_obj]
    have h := half_diamond pred
    simp [cd_is_obj] at h
    exact h
  | .pr_over pred attr_attached => _
  | .pr_miss pred attr_absent φ_absent lam_absent => _
  | .pr_Φ => prefl
  | .pr_dd => prefl
  | .pr_dc => prefl
  | .pr_cong_app premise pred => _
  | .pr_cong_dot pred => _
  | .pr_cong_obj ρ_premise premise => match ρ_premise with
    | .none => .pr_cong_obj .none (new_form_premise premise)
    | .some preduce =>
        .pr_cong_obj
          (.some (half_diamond preduce))
          (new_form_premise premise)
  | .pr_termination_refl => .pr_termination_refl
  | .pr_ξ_refl => .pr_ξ_refl
  | .pr_Φ_refl => .pr_Φ

end
