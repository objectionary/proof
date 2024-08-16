import Extended.ARS
import Extended.Term

set_option autoImplicit false

/-! ### Defition of φ-calculus term reduction `⇝` -/

open Term

structure Ctx where
  glob : Term
  scope : Term

inductive Reduce : Ctx → Term → Term → Type where
  -- Dispatch
  | r_dot
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → { t : Term }
    → lookup ρ bnds attr = LookupRes.attached t
    → Reduce ctx (dot (obj ρ bnds) attr) (substitute t (obj ρ bnds))
  | r_φ
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → lookup ρ bnds attr = LookupRes.absent
    → "φ" ∈ attrs
    → Reduce ctx (dot (obj ρ bnds) attr) (dot (dot (obj ρ bnds) "φ") attr)
  | r_stop
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → lookup ρ bnds attr = LookupRes.absent
    → lookup ρ bnds "φ" = LookupRes.absent
    → lookup ρ bnds "λ" = LookupRes.absent
    → Reduce ctx (dot (obj ρ bnds) attr) termination
  -- Application
  | r_empty
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → Reduce ctx (app (obj ρ bnds) Record.nil) (obj ρ bnds)
  | r_copy
    : { ρ : Option Term }
    → { attrs app_attrs : Attrs }
    → { bnds : Bindings attrs }
    → { app_record_tail : Record Term app_attrs }
    → { attr : Attr }
    → { not_in : attr ∉ app_attrs }
    → { g s t : Term }
    → lookup ρ bnds attr = LookupRes.void
    → Reduce
        { glob := g, scope := s }
        (app (obj ρ bnds) (Record.cons attr not_in t app_record_tail))
        (app (insert ρ bnds attr (substitute t s)) app_record_tail)
  | r_over
    : { ρ : Option Term }
    → { attrs app_attrs : Attrs }
    → { bnds : Bindings attrs }
    → { app_record_tail : Record Term app_attrs }
    → { attr : Attr }
    → { not_in : attr ∉ app_attrs }
    → { ctx : Ctx }
    → { t1 t2 : Term }
    → lookup ρ bnds attr = LookupRes.attached t1
    → Reduce
        ctx
        (app (obj ρ bnds) (Record.cons attr not_in t2 app_record_tail))
        termination
  | r_miss
    : { ρ : Option Term }
    → { attrs app_attrs : Attrs }
    → { bnds : Bindings attrs }
    → { app_record_tail : Record Term app_attrs }
    → { attr : Attr }
    → { not_in : attr ∉ app_attrs }
    → { ctx : Ctx }
    → { t : Term }
    → lookup ρ bnds attr = LookupRes.absent
    → lookup ρ bnds "φ" = LookupRes.absent
    → lookup ρ bnds "λ" = LookupRes.absent
    → Reduce
        ctx
        (app (obj ρ bnds) (Record.cons attr not_in t app_record_tail))
        termination
  -- Special terms
  | r_Φ
    : { g s : Term}
    → Reduce { glob := g, scope := s} glob g
  | r_ξ
    : { g s : Term}
    → Reduce { glob := g, scope := s} glob s
  | r_dd
    : { ctx : Ctx }
    → { attr : Attr }
    → Reduce ctx (dot termination attr) termination
  | r_dc
    : { app_attrs : Attrs }
    → { record : Record Term app_attrs }
    → { ctx : Ctx }
    → Reduce ctx (app termination record) termination
  -- Congruence
  | r_cong_appₗ
    : { ctx : Ctx }
    → {t t' : Term}
    → {app_attrs : Attrs}
    → (app_bnds : Record Term app_attrs)
    → Reduce ctx t t'
    → Reduce ctx (app t app_bnds) (app t' app_bnds)
  -- TODO: since current rules allow to add only one term from application into fomation
  -- at a time, it is reasonable to assume that congruence should only affect the term in question.
  -- This would simplify the rules. On the other hand, from the point of view of "intermediate
  -- representation for optimizations", it would make sence to allow congruence for any term of
  -- the application.
  -- | r_cong_appᵣ -- congruence of arbitrary app term
  --   : { ctx : Ctx }
  --   → {t u u' : Term}
  --   → {attr : Attr}
  --   → {app_attrs : Attrs}
  --   → (app_bnds : Record Term app_attrs)
  --   → Contains app_bnds attr u
  --   → Reduce ctx u u'
  --   → Reduce ctx (app t app_bnds) (app t (Record.insert app_bnds attr u'))
  | r_cong_appᵣ -- congruence of the first app term
    : { ctx : Ctx }
    → {t u u' : Term}
    → {attr : Attr}
    → {app_attrs : Attrs}
    → {not_in : attr ∉ app_attrs}
    → (app_bnds : Record Term app_attrs)
    → Reduce ctx u u'
    → Reduce
        ctx
        (app t (Record.cons attr not_in u app_bnds))
        (app t (Record.cons attr not_in u' app_bnds))
  | r_cong_dot
    : { ctx : Ctx }
    → {t t' : Term}
    → {attr : Attr}
    → Reduce ctx t t'
    → Reduce ctx (dot t attr) (dot t' attr)
  | r_cong_obj
    : { g l t t' : Term}
    → {ρ : Option Term}
    → {attr : Attr}
    → {attrs : Attrs}
    → {bnds : Bindings attrs}
    → Contains bnds attr (some t)
    → Reduce {glob := g, scope := obj ρ bnds} t t'
    → Reduce
        {glob := g, scope := l}
        (obj ρ bnds)
        (obj ρ (Record.insert bnds attr t'))
