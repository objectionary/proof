import Extended.ARS
import Extended.Term

set_option autoImplicit false

/-! ### Defition of φ-calculus term reduction `⇝` -/

open Term

structure Ctx where
  glob : Term
  scope : Term

inductive Reduce₁ : Ctx → Term → Term → Type where
  -- Dispatch
  | r_dot
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → { t : Term }
    → lookup ρ bnds attr = LookupRes.attached t
    → Reduce₁ ctx (dot (obj ρ bnds) attr) (substitute t (obj ρ bnds))
  | r_φ
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → lookup ρ bnds attr = LookupRes.absent
    → "φ" ∈ attrs
    → Reduce₁ ctx (dot (obj ρ bnds) attr) (dot (dot (obj ρ bnds) "φ") attr)
  | r_stop
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → { attr : Attr }
    → lookup ρ bnds attr = LookupRes.absent
    → lookup ρ bnds "φ" = LookupRes.absent
    → lookup ρ bnds "λ" = LookupRes.absent
    → Reduce₁ ctx (dot (obj ρ bnds) attr) termination
  -- Application
  | r_empty
    : { ρ : Option Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → { ctx : Ctx }
    → Reduce₁ ctx (app (obj ρ bnds) Record.nil) (obj ρ bnds)
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
    → Reduce₁
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
    → Reduce₁
        ctx
        (app (obj ρ bnds) (Record.cons attr not_in t app_record_tail))
        termination
  -- Special terms
  | r_Φ
    : { g s : Term}
    → Reduce₁ { glob := g, scope := s} glob g
  | r_dd
    : { ctx : Ctx }
    → { attr : Attr }
    → Reduce₁ ctx (dot termination attr) termination
  | r_dc
    : { app_attrs : Attrs }
    → { record : Record Term app_attrs }
    → { ctx : Ctx }
    → Reduce₁ ctx (app termination record) termination
  -- Congruence
  | r_cong_appₗ
    : { ctx : Ctx }
    → { t t' : Term }
    → { app_attrs : Attrs }
    → ( app_bnds : Record Term app_attrs )
    → Reduce₁ ctx t t'
    → Reduce₁ ctx (app t app_bnds) (app t' app_bnds)
  -- TODO: since current rules allow to add only one term from application into fomation
  -- at a time, it is reasonable to assume that congruence should only affect the term in question.
  -- This would simplify the rules. On the other hand, from the point of view of "intermediate
  -- representation for optimizations", it would make sence to allow congruence for any term of
  -- the application.
  | r_cong_appᵣ -- congruence of arbitrary app term
    : { ctx : Ctx }
    → { t u u' : Term }
    → { attr : Attr }
    → { app_attrs : Attrs }
    → ( app_bnds : Record Term app_attrs )
    → Contains app_bnds attr u
    → Reduce₁ ctx u u'
    → Reduce₁ ctx (app t app_bnds) (app t (Record.insert app_bnds attr u'))
  -- | r_cong_appᵣ -- congruence of the first app term
  --   : { ctx : Ctx }
  --   → {t u u' : Term}
  --   → {attr : Attr}
  --   → {app_attrs : Attrs}
  --   → {not_in : attr ∉ app_attrs}
  --   → (app_bnds : Record Term app_attrs)
  --   → Reduce₁ ctx u u'
  --   → Reduce₁
  --       ctx
  --       (app t (Record.cons attr not_in u app_bnds))
  --       (app t (Record.cons attr not_in u' app_bnds))
  | r_cong_dot
    : { ctx : Ctx }
    → { t t' : Term }
    → { attr : Attr }
    → Reduce₁ ctx t t'
    → Reduce₁ ctx (dot t attr) (dot t' attr)
  | r_cong_obj
    : { ctx : Ctx }
    → { t t' : Term }
    → { ρ : Option Term }
    → { attr : Attr }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → Contains bnds attr (some t)
    → Reduce₁ ctx t t'
    → Reduce₁
        ctx
        (obj ρ bnds)
        (obj ρ (Record.insert bnds attr t'))
  | r_cong_ρ
    : { ctx : Ctx }
    → { t t' : Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → Reduce₁ ctx t t'
    → Reduce₁
        ctx
        (obj (some t) bnds)
        (obj (some t') bnds)


inductive Reduce₂ : Ctx → Term → Term → Type where
  | r_ξ
    : { ctx : Ctx }
    → Reduce₂ ctx glob ctx.scope
  | r_copy
  : { ρ : Option Term }
  → { attrs app_attrs : Attrs }
  → { bnds : Bindings attrs }
  → { app_record_tail : Record Term app_attrs }
  → { attr : Attr }
  → { not_in : attr ∉ app_attrs }
  → { g s u : Term }
  → lookup ρ bnds attr = LookupRes.void
  → Reduce₂
      { glob := g, scope := s }
      (app (obj ρ bnds) (Record.cons attr not_in u app_record_tail))
      (app (insert ρ bnds attr (substitute u s)) app_record_tail)
  -- congruence
  | r_cong_appₗ
    : { ctx : Ctx }
    → { t t' : Term }
    → { app_attrs : Attrs }
    → ( app_bnds : Record Term app_attrs )
    → Reduce₂ ctx t t'
    → Reduce₂ ctx (app t app_bnds) (app t' app_bnds)
  | r_cong_appᵣ -- congruence of arbitrary app term
    : { ctx : Ctx }
    → { t u u' : Term }
    → { attr : Attr }
    → { app_attrs : Attrs }
    → (app_bnds : Record Term app_attrs)
    → Contains app_bnds attr u
    → Reduce₂ ctx u u'
    → Reduce₂ ctx (app t app_bnds) (app t (Record.insert app_bnds attr u'))
  | r_cong_dot
    : { ctx : Ctx }
    → { t t' : Term }
    → { attr : Attr }
    → Reduce₂ ctx t t'
    → Reduce₂ ctx (dot t attr) (dot t' attr)
  | r_cong_obj
    : { g l t t' : Term }
    → { ρ : Option Term }
    → { attr : Attr }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → Contains bnds attr (some t)
    → Reduce₂ {glob := g, scope := obj ρ bnds} t t'
    → Reduce₂
        {glob := g, scope := l}
        (obj ρ bnds)
        (obj ρ (Record.insert bnds attr t'))
  | r_cong_ρ
    : { g l t t' : Term }
    → { attrs : Attrs }
    → { bnds : Bindings attrs }
    → Reduce₂ {glob := g, scope := obj (some t) bnds} t t'
    → Reduce₂
        {glob := g, scope := l}
        (obj (some t) bnds)
        (obj (some t') bnds)

-- def ReducesTo (t t' : Term) := Reduce {glob := t, scope := t} t t'
-- def ReducesToMany := ReflTransGen ReducesTo

-- infix:20 " ⇝ " => ReducesTo
-- infix:20 " ⇝* " => ReducesToMany
