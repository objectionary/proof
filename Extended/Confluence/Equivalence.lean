import Extended.Term
import  Extended.Reduction.Parallel.Definition
import  Extended.Reduction.Parallel.Properties

open Term

set_option autoImplicit false

/-! ### Equivalence of `⇛` and `⇝` -/

def reg_to_par
  : {ctx : Ctx}
  → {t t' : Term}
  → Reduce ctx t t'
  → PReduce ctx t t'
  := λ reduce => match reduce with
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
  | .r_cong_appₗ app_bnds t_t' => .pr_cong_app prefl_app_premise (reg_to_par t_t')
  | .r_cong_appᵣ _ contains u_u' =>
      .pr_cong_app
        (ApplicationPremise.single _ _ (reg_to_par u_u') contains)
        prefl
  -- | .r_cong_appᵣ app_bnds contains u_u' =>
      -- .pr_cong_app
        -- (ApplicationPremise.cons (reg_to_par u_u') prefl_app_premise)
        -- prefl
  | .r_cong_dot t_t' => .pr_cong_dot (reg_to_par t_t')
  | .r_cong_obj contains t_t' =>
      .pr_cong_obj prefl_ρ_premise (FormationPremise.single _ _ (reg_to_par t_t') contains)
  | .r_cong_ρ t_t' => _

inductive R : Ctx → Term → Term → Type where
  | refl : {ctx : Ctx} → {t : Term} → R ctx t t
  | head
    : {ctx : Ctx}
    → {t s u : Term}
    → Reduce ctx t s
    → R ctx s u
    → R ctx t u

def trans_R
  {ctx : Ctx}
  {t u s : Term}
  (r1 : R ctx t u)
  (r2 : R ctx u s)
  : R ctx t s
  := match r1 with
    | .refl => r2
    | .head reduce r_tail =>
        .head reduce (trans_R r_tail r2)

def congr_dot_R
  {attr : Attr}
  {ctx : Ctx}
  {t t' : Term}
  (r : R ctx t t')
  : R ctx (dot t attr) (dot t' attr)
  := match r with
    | .refl => .refl
    | .head reduce r' => .head (.r_cong_dot reduce) (congr_dot_R r')

def congr_appₗ_R
  {attrs : Attrs}
  {apps : Record Term attrs}
  {ctx : Ctx}
  {t t' : Term}
  (r : R ctx t t')
  : R ctx (app t apps) (app t' apps)
  := match r with
    | .refl => .refl
    | .head reduce r' => .head (.r_cong_appₗ _ reduce) (congr_appₗ_R r')

def congr_appᵣ_R
  {attr : Attr}
  {attrs : Attrs}
  {apps : Record Term attrs}
  {ctx : Ctx}
  {t u u' : Term}
  (r : R ctx u u')
  (contains : Contains apps attr u)
  : R ctx (app t apps) (app t (Record.insert apps attr u'))
  := match r with
    | .refl => by
        simp [Record.insert_contains contains]
        exact .refl
    | .head reduce r' =>
        .head
          (.r_cong_appᵣ _ contains reduce)
          (by
            let temp
              : R ctx (t.app (apps.insert attr _)) (t.app ((apps.insert attr _).insert attr u'))
              := congr_appᵣ_R r' (Record.contains_after_insert contains)
            simp [Record.consequtive_insert] at temp
            exact temp
          )

def congr_obj_R
  {ctx : Ctx}
  {attrs : Attrs}
  {bnds : Bindings attrs}
  {ρ : Option Term}
  {attr : Attr}
  {t t' : Term}
  (r : R ctx t t')
  (contains : Contains bnds attr t)
  : R ctx (obj ρ bnds) (obj ρ (Record.insert bnds attr (some t')))
  := match r with
    | .refl => by
      simp [Record.insert_contains contains]
      exact .refl
    | .head reduce tail => by
      rename_i s
      have ind_hypothesis
        : R ctx
          (obj ρ (Record.insert bnds attr (some s)))
          (obj ρ (Record.insert (Record.insert bnds attr (some s)) attr (some t')))
        := congr_obj_R tail (Record.contains_after_insert contains)
      exact .head
        (.r_cong_obj contains _)
        (congr_obj_R tail contains)
      -- exact .head (.r_cong_obj contains _) (congr_obj_R tail contains)

def par_to_reg
  : {ctx : Ctx}
  → {t t' : Term}
  → PReduce ctx t t'
  → R ctx t t'
  := λ preduces => match preduces with
    | .pr_dot preduce attr_attached =>
        let reduces := par_to_reg preduce
        trans_R (congr_dot_R reduces) (.head (.r_dot attr_attached) .refl)
    | .pr_φ preduce attr_absent φ_in =>
        let reduces := par_to_reg preduce
        trans_R (congr_dot_R reduces) (.head (.r_φ attr_absent φ_in) .refl)
    | .pr_stop preduce attr_absent φ_absent lam_absent =>
        let reduces := par_to_reg preduce
        trans_R
          (congr_dot_R reduces)
          (.head (.r_stop attr_absent φ_absent lam_absent) .refl)
    | .pr_empty preduce =>
        let reduces := par_to_reg preduce
        trans_R (congr_appₗ_R reduces) (.head .r_empty .refl)
    | .pr_copy preduce_t preduce_u attr_void =>
        let reduces_t := par_to_reg preduce_t
        let reduces_u := par_to_reg preduce_u
        _
        -- trans_R
          -- (congr_appₗ_R reduces_t)
          -- (trans_R (congr_appᵣ_R reduces_u _) (.head (.r_copy attr_void) .refl))
    | .pr_over preduce attr_attached =>
        let reduces := par_to_reg preduce
        trans_R (congr_appₗ_R reduces) (.head (.r_over attr_attached) .refl)
    | .pr_miss preduce attr_absent φ_absent lam_absent =>
        let reduces := par_to_reg preduce
        trans_R
          (congr_appₗ_R reduces)
          (.head (.r_miss attr_absent φ_absent lam_absent) .refl)
    | .pr_Φ => .head .r_Φ .refl
    | .pr_ξ => .head .r_ξ .refl
    | .pr_dd => .head .r_dd .refl
    | .pr_dc => .head .r_dc .refl
    | .pr_cong_app premise preduce => trans_R
        _
        (congr_appₗ_R (par_to_reg preduce))
    | .pr_cong_dot preduce =>
        let reduces := par_to_reg preduce
        congr_dot_R reduces
    | .pr_cong_obj ρ_premise premise => _
    | .pr_termination_refl => .refl
    | .pr_ξ_refl => .refl
    | .pr_Φ_refl => .refl


-- def par_to_reg
--   : {t t' : Term}
--   → PReducesTo t t'
--   → ReducesToMany t t'
--   := λ preduces => match preduces with
--     | .pr_dot preduce attr_attached => _
--     | .pr_φ preduce attr_absent φ_in => _
--     | .pr_stop preduce attr_absent φ_absent lam_absent => _
--     | .pr_empty preduce => _
--     | .pr_copy preduce_t preduce_u attr_void => _
--     | .pr_over preduce attr_attached => _
--     | .pr_miss preduce attr_absent φ_absent lam_absent => _
--     | .pr_Φ => .head .r_Φ .refl
--     | .pr_ξ => .head .r_ξ .refl
--     | .pr_dd => .head .r_dd .refl
--     | .pr_dc => .head .r_dc .refl
--     | .pr_cong_app premise preduce => _
--     | .pr_cong_dot preduce =>
--         let reduce := par_to_reg preduce
--         _
--     | .pr_cong_obj premise => _
--     | .pr_termination_refl => .refl
--     | .pr_ξ_refl => .refl
--     | .pr_Φ_refl => .refl
