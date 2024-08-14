import Extended.Term
import  Extended.Reduction.Parallel.Definition
import  Extended.Reduction.Parallel.Properties

open Term

set_option autoImplicit false

/-! ### Equivalence of `⇛` and `⇝` -/

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (1)] -/
def reg_to_par
  : {ctx : Ctx}
  → {t t' : Term}
  → Reduce ctx t t'
  → PReduce ctx t t'
  -- := λ { ctx t t' } reduce => match reduce with
  := λ { _ _ _ } reduce => match reduce with
    -- Dispatch
  | .r_dot is_attached => .pr_dot prefl is_attached
  | .r_φ attr_absent φ_present => .pr_φ prefl attr_absent φ_present
  | .r_stop attr_absent φ_absent lam_absent => .pr_stop prefl attr_absent φ_absent lam_absent
  -- Application
  | .r_empty => .pr_empty prefl
  | .r_copy attr_void => .pr_copy prefl prefl attr_void
  | .r_over attr_attached => .pr_over prefl attr_attached
  | .r_miss attr_absent φ_absent lam_absent => .pr_miss prefl attr_absent φ_absent lam_absent
  -- Special terms
  | .r_Φ => .pr_Φ
  | .r_ξ => .pr_ξ
  | .r_dd => .pr_dd
  | .r_dc => .pr_dc
  -- Congruence
  | .r_cong_appₗ t t' app_bnds t_t' => .pr_cong_app prefl_app_premise (reg_to_par t_t')
  | .r_cong_appᵣ app_bnds u_u' =>
      .pr_cong_app
        (ApplicationPremise.cons (reg_to_par u_u') prefl_app_premise)
        prefl
  | .r_cong_dot t_t' => .pr_cong_dot (reg_to_par t_t')
  -- TODO
  | .r_cong_obj contains t_t' => .pr_cong_obj (FormationPremise.single (reg_to_par _) contains)
