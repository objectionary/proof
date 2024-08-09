import Extended.Term

set_option autoImplicit false

/-! ### Defition of φ-calculus term reduction `⇝` -/

open Term

structure Ctx where
  glob : Term
  scope : Term

inductive Reduce : Ctx → Term → Term → Type where
  | r_Φ
    : { g s : Term}
    → Reduce { glob := g, scope := s} glob g
  | r_ξ
    : { g s : Term}
    → Reduce { glob := g, scope := s} glob s
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
  | r_dd
    : { ctx : Ctx }
    → { attr : Attr }
    → Reduce ctx (dot termination attr) termination
  | r_dc
    : { app_attrs : Attrs }
    → { record : Record Term app_attrs }
    → { ctx : Ctx }
    → Reduce ctx (app termination record) termination
