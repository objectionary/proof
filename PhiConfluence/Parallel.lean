-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.LocalConfluence
import PhiConfluence.WellFormed
import PhiConfluence.Nf
import PhiConfluence.Context

/-!
# Parallel reduction `Par`

Parallel reduction contracts any set of redexes in one step, including inside
subterms and formation bindings — congruence is built in. It is the relation whose
**diamond** (Takahashi complete development, guard-on-developed-subterm) gives confluence
via `Relation.church_rosser`; see README "Proof strategy".

`Par` and `ParB` are **mutually inductive** (`ParB` reduces a binding list pointwise),
with a *bespoke cons-structured* `ParB` — the `List.Forall₂ ParBind` alternative is
kernel-rejected as a nested inductive carrying `Par`. The append index of `Step.congForm`
is crossed exactly once, by `parB_set`.

This module connects `Step` and `Par` (`step_to_par`, `par_to_red`, the headline `redMany_eq` :
`ReflTransGen Step = ReflTransGen Par`) and builds the **Takahashi triangle**: the total complete
development `devel`/`develB`, `par_devel` (`e ⇒ devel e`), the `ParB` inversions, and
`par_triangle` (`WF e → Par e u → Par u (devel e)`; the hypothesis is threaded through but no
case consumes it). The triangle feeds `Diamond.lean`'s
`parWF_diamond` and, via `redMany_eq`, `Confluence.lean`'s headline `confluence`.

Besides one constructor per `Step` rule, `Par` has `ddl` and `dcl`: a dispatch or an application
on a formation holding both `λ` and `Δ` collapses to `⊥` in one parallel step (`dl` inside, then
`dd`/`dc` outside). They let `devel` answer `⊥` for such a redex whichever rule fires first.

Note: the discard constructors carry premises (`ParB bs bs'`, `Par e e'`) that are unused in their
`⊥` result, and `stay` and `skip` carry an unused argument-`Par`. This is the standard parallel-reduction
shape — a single `⇒` step may develop subterms even while collapsing.
-/

namespace PhiConfluence

mutual

/-- Parallel reduction: contracts a set of redexes (and reduces inside subterms and
binding values) in one step. -/
inductive Par : Term → Term → Prop where
  | refl (e : Term) : Par e e
  | dd (a : Attr) : Par (.dispatch .bot a) .bot
  | dc {a : Attr} {e e' : Term} : Par e e' → Par (.app .bot a e) .bot
  | null {bs bs' : List Binding} {a : Attr} :
      ParB bs bs' → lookup bs a = .void → Par (.dispatch (.form bs) a) .bot
  | over {bs bs' : List Binding} {a : Attr} {e₁ e₂ e₂' : Term} :
      ParB bs bs' → lookup bs a = .attached e₁ → a ≠ .rho → Par e₂ e₂' →
      Par (.app (.form bs) a e₂) .bot
  | stop {bs bs' : List Binding} {a : Attr} :
      ParB bs bs' → lookup bs a = .absent → lookup bs .phi = .absent → hasLambda bs = false →
      Par (.dispatch (.form bs) a) .bot
  | norho {bs bs' : List Binding} :
      ParB bs bs' → lookup bs .rho = .absent → Par (.dispatch (.form bs) .rho) .bot
  | miss {bs bs' : List Binding} {a : Attr} {e e' : Term} :
      ParB bs bs' → lookup bs a = .absent → a ≠ .rho → Par e e' →
      Par (.app (.form bs) a e) .bot
  | stay {bs bs' : List Binding} {e₁ e₂ e₂' : Term} :
      ParB bs bs' → lookup bs .rho = .attached e₁ → Par e₂ e₂' →
      Par (.app (.form bs) .rho e₂) (.form bs')
  | skip {bs bs' : List Binding} {e e' : Term} :
      ParB bs bs' → lookup bs .rho = .absent → Par e e' →
      Par (.app (.form bs) .rho e) (.form bs')
  | dot {bs bs' : List Binding} {a : Attr} {e₀ e₁ : Term} :
      ParB bs bs' → lookup bs a = .attached e₀ → lookup bs' a = .attached e₁ → nf e₁ = true →
      (hasLambda bs && hasDelta bs) = false →
      Par (.dispatch (.form bs) a)
        (.app (contextualize e₁ (.form (erase bs' a))) .rho (.form bs'))
  | copy {bs bs' : List Binding} {a : Attr} {arg arg' : Term} :
      ParB bs bs' → lookup bs a = .void → Par arg arg' → xiFree arg' = true → nf arg' = true →
      Par (.app (.form bs) a arg) (.form (fill bs' a arg'))
  | dl {bs : List Binding} :
      hasLambda bs = true → hasDelta bs = true → Par (.form bs) .bot
  | ddl {bs : List Binding} {a : Attr} :
      hasLambda bs = true → hasDelta bs = true → Par (.dispatch (.form bs) a) .bot
  | dcl {bs : List Binding} {a : Attr} {e : Term} :
      hasLambda bs = true → hasDelta bs = true → Par (.app (.form bs) a e) .bot
  | congDispatch {e e' : Term} {a : Attr} :
      Par e e' → Par (.dispatch e a) (.dispatch e' a)
  | congApp {e e' : Term} {a : Attr} {arg arg' : Term} :
      Par e e' → Par arg arg' → Par (.app e a arg) (.app e' a arg')
  | congForm {bs bs' : List Binding} : ParB bs bs' → Par (.form bs) (.form bs')

/-- Pointwise parallel reduction of a binding list (values reduce; keys/shape fixed). -/
inductive ParB : List Binding → List Binding → Prop where
  | nil : ParB [] []
  | consVoid {a : Attr} {bs bs' : List Binding} :
      ParB bs bs' → ParB (.void a :: bs) (.void a :: bs')
  | consAttached {a : Attr} {v v' : Term} {bs bs' : List Binding} :
      Par v v' → ParB bs bs' → ParB (.attached a v :: bs) (.attached a v' :: bs')
  | consDelta {d : List UInt8} {bs bs' : List Binding} :
      ParB bs bs' → ParB (.delta d :: bs) (.delta d :: bs')
  | consLambda {f : String} {bs bs' : List Binding} :
      ParB bs bs' → ParB (.lambda f :: bs) (.lambda f :: bs')

end

/-- Parallel reduction is reflexive on binding lists (each value reduces to itself). -/
theorem ParB.refl' : ∀ (bs : List Binding), ParB bs bs
  | [] => .nil
  | .void _ :: r => .consVoid (ParB.refl' r)
  | .attached _ v :: r => .consAttached (.refl v) (ParB.refl' r)
  | .delta _ :: r => .consDelta (ParB.refl' r)
  | .lambda _ :: r => .consLambda (ParB.refl' r)

/-- `ParB` lifts through `fill`: a pointwise binding-list reduction survives a slot-fill (the
filled slot becomes `consAttached (Par.refl v)`; the others recurse — `ParB` shares shape, so no
lookup hypothesis is needed). The engine behind the triangle's `copy` case. -/
theorem parB_fill {cs ds : List Binding} (h : ParB cs ds) (a : Attr) (v : Term) :
    ParB (fill cs a v) (fill ds a v) := by
  induction h using ParB.rec (motive_1 := fun _ _ _ => True) with
  | nil => exact .nil
  | consVoid hb ih =>
      rename_i c bs bs'
      simp only [fill]
      by_cases hc : c = a
      · subst hc; simp only [if_true]; exact .consAttached (.refl v) hb
      · simp only [if_neg hc]; exact .consVoid ih
  | consAttached hvv hb ihv ihb =>
      rename_i c v0 v0' bs bs'
      simp only [fill]
      by_cases hc : c = a
      · subst hc; simp only [if_true]; exact .consAttached hvv hb
      · simp only [if_neg hc]; exact .consAttached hvv ihb
  | consDelta hb ih =>
      rename_i d bs bs'
      simp only [fill]; exact .consDelta ih
  | consLambda hb ih =>
      rename_i f bs bs'
      simp only [fill]; exact .consLambda ih
  | _ => trivial

/-- `ParB` lifts through `erase`: dropping the same key from both lists keeps them pointwise
related. The engine behind the triangle's `dot` context. -/
theorem parB_erase {cs ds : List Binding} (h : ParB cs ds) (a : Attr) :
    ParB (erase cs a) (erase ds a) := by
  induction h using ParB.rec (motive_1 := fun _ _ _ => True) with
  | nil => exact .nil
  | consVoid hb ih =>
      rename_i c bs bs'
      simp only [erase]
      by_cases hc : c = a
      · simp only [if_pos hc]; exact hb
      · simp only [if_neg hc]; exact .consVoid ih
  | consAttached hvv hb ihv ihb =>
      rename_i c v0 v0' bs bs'
      simp only [erase]
      by_cases hc : c = a
      · simp only [if_pos hc]; exact hb
      · simp only [if_neg hc]; exact .consAttached hvv ihb
  | consDelta hb ih => simp only [erase]; exact .consDelta ih
  | consLambda hb ih => simp only [erase]; exact .consLambda ih
  | _ => trivial

/-- Reducing one attached binding's value lifts to a pointwise binding-list reduction
(the bridge across `Step.congForm`'s append index). -/
theorem parB_set {bs₁ bs₂ : List Binding} {a : Attr} {e e' : Term} (h : Par e e') :
    ParB (bs₁ ++ .attached a e :: bs₂) (bs₁ ++ .attached a e' :: bs₂) := by
  induction bs₁ with
  | nil => exact ParB.consAttached h (ParB.refl' bs₂)
  | cons b r ih =>
      cases b with
      | void c => exact ParB.consVoid ih
      | attached c v => exact ParB.consAttached (.refl v) ih
      | delta d => exact ParB.consDelta ih
      | lambda f => exact ParB.consLambda ih

/-- `ParB` preserves each attribute's lookup-shape (`void`/`absent`/`attached`) and the
`hasLambda`/`hasDelta` flags: it reduces values, never keys, presence, or assets. The engine
behind the triangle's side-condition transport (a redex's guard still holds on the developed
binding list). -/
theorem parB_preserves {bs bs' : List Binding} (h : ParB bs bs') :
    (∀ a, lookup bs a = .void → lookup bs' a = .void)
      ∧ (∀ a, lookup bs a = .absent → lookup bs' a = .absent)
      ∧ (∀ a v, lookup bs a = .attached v → ∃ w, lookup bs' a = .attached w)
      ∧ hasLambda bs = hasLambda bs' ∧ hasDelta bs = hasDelta bs' := by
  induction h using ParB.rec (motive_1 := fun _ _ _ => True) with
  | nil => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [lookup, hasLambda, hasDelta]
  | consVoid hb ih =>
      obtain ⟨iv, ia, iat, il, id⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · next hc => rw [if_pos hc]
        · next hc => rw [if_neg hc]; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact iat a v ha
      · simp only [hasLambda]; exact il
      · simp only [hasDelta]; exact id
  | consAttached hvv hb _ ih =>
      obtain ⟨iv, ia, iat, il, id⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; split at ha
        · next hc => rw [if_pos hc]; exact ⟨_, rfl⟩
        · next hc => rw [if_neg hc]; exact iat a v ha
      · simp only [hasLambda]; exact il
      · simp only [hasDelta]; exact id
  | consDelta hb ih =>
      obtain ⟨iv, ia, iat, il, id⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; exact iat a v ha
      · simp only [hasLambda]; exact il
      · simp only [hasDelta]
  | consLambda hb ih =>
      obtain ⟨iv, ia, iat, il, id⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; exact iat a v ha
      · simp only [hasLambda]
      · simp only [hasDelta]; exact id
  | _ => trivial

/-- `ParB` keeps a `void` slot `void`. -/
theorem parB_lookup_void {bs bs' : List Binding} (h : ParB bs bs') {a : Attr}
    (ha : lookup bs a = .void) : lookup bs' a = .void := (parB_preserves h).1 a ha
/-- `ParB` keeps an `absent` slot `absent`. -/
theorem parB_lookup_absent {bs bs' : List Binding} (h : ParB bs bs') {a : Attr}
    (ha : lookup bs a = .absent) : lookup bs' a = .absent := (parB_preserves h).2.1 a ha
/-- `ParB` keeps an `attached` slot attached (to some developed value). -/
theorem parB_lookup_attached {bs bs' : List Binding} (h : ParB bs bs') {a : Attr} {v : Term}
    (ha : lookup bs a = .attached v) : ∃ w, lookup bs' a = .attached w := (parB_preserves h).2.2.1 a v ha
/-- `ParB` preserves the `hasLambda` flag. -/
theorem parB_hasLambda {bs bs' : List Binding} (h : ParB bs bs') :
    hasLambda bs = hasLambda bs' := (parB_preserves h).2.2.2.1
/-- `ParB` preserves the `hasDelta` flag. -/
theorem parB_hasDelta {bs bs' : List Binding} (h : ParB bs bs') :
    hasDelta bs = hasDelta bs' := (parB_preserves h).2.2.2.2

/-- `ParB` keeps an attribute present: a slot that is not `absent` stays not `absent`. -/
theorem parB_lookup_present {bs bs' : List Binding} (h : ParB bs bs') {a : Attr}
    (ha : lookup bs a ≠ .absent) : lookup bs' a ≠ .absent := by
  cases hl : lookup bs a with
  | absent => exact absurd hl ha
  | void => rw [parB_lookup_void h hl]; nofun
  | attached v => obtain ⟨w, hw⟩ := parB_lookup_attached h hl; rw [hw]; nofun

/-- `fill` keeps the assets, so it keeps the `hasLambda` flag. -/
theorem hasLambda_fill (bs : List Binding) (a : Attr) (v : Term) :
    hasLambda (fill bs a v) = hasLambda bs := by
  induction bs with
  | nil => rfl
  | cons b r ih =>
      cases b with
      | void c => by_cases hc : c = a <;> simp [fill, hasLambda, hc, ih]
      | attached c w => by_cases hc : c = a <;> simp [fill, hasLambda, hc, ih]
      | delta d => simp [fill, hasLambda, ih]
      | lambda f => simp [fill, hasLambda]

/-- `fill` keeps the assets, so it keeps the `hasDelta` flag. -/
theorem hasDelta_fill (bs : List Binding) (a : Attr) (v : Term) :
    hasDelta (fill bs a v) = hasDelta bs := by
  induction bs with
  | nil => rfl
  | cons b r ih =>
      cases b with
      | void c => by_cases hc : c = a <;> simp [fill, hasDelta, hc, ih]
      | attached c w => by_cases hc : c = a <;> simp [fill, hasDelta, hc, ih]
      | delta d => simp [fill, hasDelta]
      | lambda f => simp [fill, hasDelta, ih]

/-- Every single step is a parallel step (`Step ⊆ Par`). -/
theorem step_to_par {e e' : Term} (h : e ↝ e') : Par e e' := by
  induction h with
  | dd a => exact .dd a
  | dc a e => exact .dc (.refl e)
  | null hv => exact .null (ParB.refl' _) hv
  | «over» hatt hne => exact .over (ParB.refl' _) hatt hne (.refl _)
  | stop habs hphi hlam => exact .stop (ParB.refl' _) habs hphi hlam
  | norho habs => exact .norho (ParB.refl' _) habs
  | miss habs hne => exact .miss (ParB.refl' _) habs hne (.refl _)
  | stay hs => exact .stay (ParB.refl' _) hs (.refl _)
  | skip hs => exact .skip (ParB.refl' _) hs (.refl _)
  | dot hl hnf hld => exact .dot (ParB.refl' _) hl hl hnf hld
  | copy hl hxi hnf => exact .copy (ParB.refl' _) hl (.refl _) hxi hnf
  | dl hl hd => exact .dl hl hd
  | congDispatch _ ih => exact .congDispatch ih
  | congAppFn _ ih => exact .congApp ih (.refl _)
  | congAppArg _ ih => exact .congApp (.refl _) ih
  | congForm _ ih => exact .congForm (parB_set ih)

/-- A single step between formations lifts by prepending a binding (it is a `congForm`
on the extended prefix; `dl` cannot land on a formation). -/
theorem step_form_cons {bs bs' : List Binding} (b : Binding) (h : Step (.form bs) (.form bs')) :
    Step (.form (b :: bs)) (.form (b :: bs')) := by
  rcases form_step_inv h with ⟨cs₁, c, f, f', cs₂, hbs, hbs', hf⟩ | ⟨hb, _, _⟩
  · subst hbs
    injection hbs' with hbs'
    subst hbs'
    exact Step.congForm (bs₁ := b :: cs₁) hf
  · nomatch hb

/-- Nothing steps out of `⊥`. -/
theorem bot_step_inv {t : Term} (h : Step .bot t) : False := by
  cases h

/-- Anything reachable from a formation is a formation or `⊥` (a formation steps by `congForm`
or collapses by `dl`, and `⊥` is stuck). -/
theorem redMany_form_target {bs : List Binding} {t : Term} (h : (Term.form bs) ↝∗ t) :
    t = .bot ∨ ∃ cs, t = .form cs := by
  induction h with
  | refl => exact .inr ⟨bs, rfl⟩
  | tail _ hstep ih =>
      rcases ih with rfl | ⟨cs, rfl⟩
      · exact (bot_step_inv hstep).elim
      · rcases form_step_inv hstep with ⟨_, _, _, _, _, _, ht, _⟩ | ⟨ht, _, _⟩
        · exact .inr ⟨_, ht⟩
        · exact .inl ht

/-- Multi-step reduction between formations lifts by prepending a binding — proved by
hand (NOT `ReflTransGen.lift`, which is unsound here since `stay` turns app→form, so
prepend-`b` is not a step homomorphism). -/
theorem redMany_form_cons {bs : List Binding} (b : Binding) {t : Term}
    (h : (Term.form bs) ↝∗ t) :
    ∀ {bs' : List Binding}, t = .form bs' → (Term.form (b :: bs)) ↝∗ (Term.form (b :: bs')) := by
  induction h with
  | refl => intro bs' ht; injection ht with h2; subst h2; exact .refl
  | tail h1 hstep ih =>
      intro bs' ht
      subst ht
      rcases redMany_form_target h1 with hc | ⟨cs, hc⟩
      · subst hc; exact (bot_step_inv hstep).elim
      · subst hc
        exact (ih rfl).tail (step_form_cons b hstep)

/-- Every parallel step is realized by zero-or-more single steps (`Par ⊆ Step∗`). Proved
by the two-motive mutual recursor: `motive₂` on a binding-list reduction is the
corresponding formation reduction. -/
theorem par_to_red {e e' : Term} (h : Par e e') : e ↝∗ e' := by
  induction h using Par.rec
    (motive_2 := fun bs bs' _ => (Term.form bs) ↝∗ (Term.form bs')) with
  | refl e => exact .refl
  | dd a => exact .single (Step.dd a)
  | dc => exact .single (Step.dc _ _)
  | null hb hl ihb => exact .single (Step.null hl)
  | «over» hb hl hne he ihb ihe => exact .single (Step.over hl hne)
  | stop hb h1 h2 h3 ihb => exact .single (Step.stop h1 h2 h3)
  | norho hb hl ihb => exact .single (Step.norho hl)
  | miss hb hl hne he ihb ihe => exact .single (Step.miss hl hne)
  | stay hb hl he ihb ihe => exact .head (Step.stay hl) ihb
  | skip hb hl he ihb ihe => exact .head (Step.skip hl) ihb
  | dot hb hl0 hl1 hnf hld ihb =>
      rename_i bs bs' a e₀ e₁
      have hld' : (hasLambda bs' && hasDelta bs') = false := by
        rw [← parB_hasLambda hb, ← parB_hasDelta hb]; exact hld
      exact (redMany_congDispatch _ ihb).tail (Step.dot hl1 hnf hld')
  | copy hb hl harg hxi hnf ihb iharg =>
      exact ((redMany_congAppFn _ _ ihb).trans (redMany_congAppArg _ _ iharg)).tail
        (Step.copy (parB_lookup_void hb hl) hxi hnf)
  | dl hl hd => exact .single (Step.dl hl hd)
  | ddl hl hd => exact .head (Step.congDispatch (Step.dl hl hd)) (.single (Step.dd _))
  | dcl hl hd => exact .head (Step.congAppFn (Step.dl hl hd)) (.single (Step.dc _ _))
  | congDispatch he ih => exact redMany_congDispatch _ ih
  | congApp he harg ihe iharg =>
      exact (redMany_congAppFn _ _ ihe).trans (redMany_congAppArg _ _ iharg)
  | congForm hb ihb => exact ihb
  | nil => exact .refl
  | consVoid hb ihb => exact redMany_form_cons _ ihb rfl
  | consAttached hv hb ihv ihb =>
      exact (redMany_congForm (bs₁ := []) ihv).trans (redMany_form_cons _ ihb rfl)
  | consDelta hb ihb => exact redMany_form_cons _ ihb rfl
  | consLambda hb ihb => exact redMany_form_cons _ ihb rfl

/-- Single-step and parallel reduction have the *same*
reflexive-transitive closure (`Step ⊆ Par ⊆ Step∗`). So confluence of `Par` transports
to confluence of `Step`. -/
theorem redMany_eq : RedMany = Relation.ReflTransGen Par := by
  funext a b
  apply propext
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ st ih => exact ih.tail (step_to_par st)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ pt ih => exact ih.trans (par_to_red pt)

/-- The development of a dispatch `⟦bs⟧.a` on a formation without both `λ` and `Δ`, given the
developed bindings `bsd`: `null`, `stop` and `norho` collapse it, `dot` fires when the developed value is
normal (contextualized against the developed formation without `a`), anything else develops
inside. -/
def develDispatch (bs bsd : List Binding) (a : Attr) : Term :=
  match lookup bs a with
  | .void => .bot
  | .attached _ =>
      match lookup bsd a with
      | .attached e₁ =>
          if nf e₁ then .app (contextualize e₁ (.form (erase bsd a))) .rho (.form bsd)
          else .dispatch (.form bsd) a
      | _ => .dispatch (.form bsd) a
  | .absent =>
      if a = .rho then .bot else
      match lookup bs .phi with
      | .absent => if hasLambda bs then .dispatch (.form bsd) a else .bot
      | _ => .dispatch (.form bsd) a

/-- The development of an application `⟦bs⟧(a ↦ e)`, given the developed bindings `bsd` and argument `argd`: `stay` and `skip` keep the formation, `over` and `miss` collapse it,
`copy` fills the void slot when the developed argument is `ξ`-free and normal. -/
def develAttr (bs bsd : List Binding) (a : Attr) (argd : Term) : Term :=
  match lookup bs a with
  | .attached _ => if a = .rho then .form bsd else .bot
  | .absent => if a = .rho then .form bsd else .bot
  | .void => if xiFree argd && nf argd then .form (fill bsd a argd) else .app (.form bsd) a argd

mutual

/-- **Complete development** (Takahashi's `e*`): contract *every* redex present in `e` in one
sweep. It is the apex of the `Par`-diamond — `par_triangle` shows any single `⇒` out of a
well-formed `e` is itself followed by a `⇒` into `devel e`, so `d := devel a` joins any fork.
A formation holding both `λ` and `Δ` develops to `⊥`, and so does every dispatch and application
on it, since `dl` wins every fork there. -/
def devel : Term → Term
  | .bot => .bot
  | .glob => .glob
  | .xi => .xi
  | .form bs => if hasLambda bs && hasDelta bs then .bot else .form (develB bs)
  | .dispatch .bot _ => .bot
  | .dispatch (.form bs) a =>
      if hasLambda bs && hasDelta bs then .bot else develDispatch bs (develB bs) a
  | .dispatch e a => .dispatch (devel e) a
  | .app .bot _ _ => .bot
  | .app (.form bs) a e₂ =>
      if hasLambda bs && hasDelta bs then .bot else develAttr bs (develB bs) a (devel e₂)
  | .app e a e₂ => .app (devel e) a (devel e₂)

/-- Complete development of a binding list (develop every attached value, keys/shape fixed). -/
def develB : List Binding → List Binding
  | [] => []
  | .void a :: rest => .void a :: develB rest
  | .attached a v :: rest => .attached a (devel v) :: develB rest
  | .delta d :: rest => .delta d :: develB rest
  | .lambda f :: rest => .lambda f :: develB rest
end

/-- `devel` of a formation, unfolded. -/
theorem devel_form (bs : List Binding) :
    devel (.form bs) = if hasLambda bs && hasDelta bs then .bot else .form (develB bs) := by
  simp only [devel]

/-- `devel` of a dispatch on a formation, unfolded. -/
theorem devel_dispatch (bs : List Binding) (a : Attr) :
    devel (.dispatch (.form bs) a)
      = if hasLambda bs && hasDelta bs then .bot else develDispatch bs (develB bs) a := by
  simp only [devel]

/-- `devel` of an application on a formation, unfolded. -/
theorem devel_attr (bs : List Binding) (a : Attr) (e : Term) :
    devel (.app (.form bs) a e)
      = if hasLambda bs && hasDelta bs then .bot else develAttr bs (develB bs) a (devel e) := by
  simp only [devel]

/-- `develB` develops the value found by `lookup` — the bridge `devel`'s `dot` arm uses to read
the developed dispatched value back (via `lookup (develB bs) a`), keeping `devel` structurally
recursive (it never calls `devel` on a value extracted by `lookup`). -/
theorem lookup_develB : ∀ (bs : List Binding) (a : Attr) (e₁ : Term),
    lookup bs a = .attached e₁ → lookup (develB bs) a = .attached (devel e₁) := by
  intro bs
  induction bs with
  | nil => intro a e₁ h; simp [lookup] at h
  | cons b r ih =>
      intro a e₁ h
      cases b with
      | void c =>
          simp only [lookup] at h
          simp only [develB, lookup]
          split at h
          · nomatch h
          · next hc => rw [if_neg hc]; exact ih a e₁ h
      | attached c v =>
          simp only [lookup] at h
          simp only [develB, lookup]
          split at h
          · next hc =>
              rw [if_pos hc]
              injection h with hv; subst hv; rfl
          · next hc => rw [if_neg hc]; exact ih a e₁ h
      | delta d =>
          simp only [lookup] at h
          simp only [develB, lookup]
          exact ih a e₁ h
      | lambda f =>
          simp only [lookup] at h
          simp only [develB, lookup]
          exact ih a e₁ h

/-- A formation holding both `λ` and `Δ` reaches `⊥` in one parallel step from any `ParB`-reduct
of its bindings. -/
theorem par_dl {bs bs' : List Binding} (h : ParB bs bs') (hl : hasLambda bs = true)
    (hd : hasDelta bs = true) : Par (.form bs') .bot :=
  .dl (by rw [← parB_hasLambda h]; exact hl) (by rw [← parB_hasDelta h]; exact hd)

/-- A `Par`-reduct of a formation is a formation with pointwise-reduced bindings, or `⊥` when
the formation holds both `λ` and `Δ` (the `Par`-level analogue of `form_step_inv`). -/
theorem par_form_inv {bs : List Binding} {t : Term} (h : Par (.form bs) t) :
    (∃ cs, t = .form cs ∧ ParB bs cs) ∨ (t = .bot ∧ hasLambda bs = true ∧ hasDelta bs = true) := by
  cases h with
  | refl => exact .inl ⟨bs, rfl, ParB.refl' bs⟩
  | congForm hpb => rename_i cs; exact .inl ⟨cs, rfl, hpb⟩
  | dl hl hd => exact .inr ⟨rfl, hl, hd⟩

/-- A `Par`-reduct of a formation without both `λ` and `Δ` is a formation. -/
theorem par_form_inv' {bs : List Binding} {t : Term} (h : Par (.form bs) t)
    (hld : (hasLambda bs && hasDelta bs) = false) : ∃ cs, t = .form cs ∧ ParB bs cs := by
  rcases par_form_inv h with hc | ⟨_, hl, hd⟩
  · exact hc
  · simp [hl, hd] at hld

/-- `par_devel` for an application on a formation, given the argument's development and
bindings. -/
theorem par_devel_attr {bs : List Binding} {a : Attr} {e₂ : Term}
    (hb : ParB bs (develB bs)) (he : Par e₂ (devel e₂)) : Par (.app (.form bs) a e₂) (devel (.app (.form bs) a e₂)) := by
  rw [devel_attr bs a]
  by_cases hld : (hasLambda bs && hasDelta bs) = true
  · obtain ⟨hl, hd⟩ := Bool.and_eq_true_iff.mp hld
    rw [if_pos hld]; exact .dcl hl hd
  · rw [if_neg hld]
    simp only [develAttr]
    match h : lookup bs a with
    | .attached v =>
        by_cases hr : a = .rho
        · subst hr; simp only [if_true]; exact .stay hb h he
        · simp only [hr, if_false]; exact .over hb h hr he
    | .absent =>
        by_cases hr : a = .rho
        · subst hr; simp only [if_true]; exact .skip hb h he
        · simp only [hr, if_false]; exact .miss hb h hr he
    | .void =>
        by_cases hcp : xiFree (devel e₂) && nf (devel e₂)
        · obtain ⟨hxi, hnf⟩ := Bool.and_eq_true_iff.mp hcp
          simp only [hcp, if_true]
          exact .copy hb h he hxi hnf
        · simp only [hcp, Bool.false_eq_true, if_false]
          exact .congApp (.congForm hb) he

mutual

/-- `e ⇒ devel e`: every term parallel-reduces to its own complete development (the
reflexive apex of the triangle; reused by the congruence helpers). -/
theorem par_devel : ∀ (e : Term), Par e (devel e)
  | .bot => .refl _
  | .glob => .refl _
  | .xi => .refl _
  | .form bs => by
      rw [devel_form]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl, hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]; exact .dl hl hd
      · rw [if_neg hld]; exact .congForm (parB_develB bs)
  | .dispatch .bot a => .dd a
  | .dispatch (.form bs) a => by
      rw [devel_dispatch]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl, hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]; exact .ddl hl hd
      · rw [if_neg hld]
        simp only [Bool.not_eq_true] at hld
        simp only [develDispatch]
        match h : lookup bs a with
        | .void => exact .null (parB_develB bs) h
        | .attached v =>
            have hd : lookup (develB bs) a = .attached (devel v) := lookup_develB bs a v h
            simp only [hd]
            by_cases hnf : nf (devel v)
            · simp only [hnf, if_true]
              exact .dot (parB_develB bs) h hd hnf hld
            · simp only [hnf, Bool.false_eq_true, if_false]
              exact .congDispatch (.congForm (parB_develB bs))
        | .absent =>
            by_cases hr : a = .rho
            · subst hr; simp only [if_true]; exact .norho (parB_develB bs) h
            simp only [hr, if_false]
            match hphi : lookup bs .phi with
            | .absent =>
                by_cases hl : hasLambda bs = true
                · simp only [hl, if_true]; exact .congDispatch (.congForm (parB_develB bs))
                · simp only [Bool.not_eq_true] at hl
                  simp only [hl, Bool.false_eq_true, if_false]
                  exact .stop (parB_develB bs) h hphi hl
            | .void => exact .congDispatch (.congForm (parB_develB bs))
            | .attached _ => exact .congDispatch (.congForm (parB_develB bs))
  | .dispatch .glob a => .congDispatch (.refl _)
  | .dispatch .xi a => .congDispatch (.refl _)
  | .dispatch (.dispatch s b) a => .congDispatch (par_devel _)
  | .dispatch (.app s b arg) a => .congDispatch (par_devel _)
  | .app .bot a e₂ => .dc (par_devel e₂)
  | .app (.form bs) .phi e₂ => par_devel_attr (parB_develB bs) (par_devel e₂)
  | .app (.form bs) .rho e₂ => par_devel_attr (parB_develB bs) (par_devel e₂)
  | .app (.form bs) (.label nm) e₂ => par_devel_attr (parB_develB bs) (par_devel e₂)
  | .app .glob a e₂ => .congApp (.refl _) (par_devel e₂)
  | .app .xi a e₂ => .congApp (.refl _) (par_devel e₂)
  | .app (.dispatch s c) a e₂ => .congApp (par_devel _) (par_devel e₂)
  | .app (.app s c arg) a e₂ => .congApp (par_devel _) (par_devel e₂)

/-- `ParB` companion of `par_devel`: every binding list develops to `develB`. -/
theorem parB_develB : ∀ (bs : List Binding), ParB bs (develB bs)
  | [] => .nil
  | .void _ :: rest => .consVoid (parB_develB rest)
  | .attached _ v :: rest => .consAttached (par_devel v) (parB_develB rest)
  | .delta _ :: rest => .consDelta (parB_develB rest)
  | .lambda _ :: rest => .consLambda (parB_develB rest)
end

/-- `ParB` develops the attached value, exposing the witnessing `Par`: if `bs` has `a ↦ v`
attached, then `bs'` has `a ↦ w` attached with `Par v w`. The engine behind the triangle's `dot`
case (combined with `nf_par_eq` it pins the developed value to the `dot`-redex's `nf` value). -/
theorem parB_lookup_attached_par {bs bs' : List Binding} (h : ParB bs bs') {a : Attr} {v : Term}
    (hl : lookup bs a = .attached v) : ∃ w, lookup bs' a = .attached w ∧ Par v w := by
  induction h using ParB.rec (motive_1 := fun _ _ _ => True) with
  | nil => simp [lookup] at hl
  | consVoid hb ih =>
      rename_i c _ _
      simp only [lookup] at hl ⊢
      split at hl
      · nomatch hl
      · next hc => rw [if_neg hc]; exact ih hl
  | consAttached hvv hb ihv ihb =>
      rename_i c v0 v0' _ _
      simp only [lookup] at hl ⊢
      split at hl
      · next hc =>
          rw [if_pos hc]
          injection hl with hvv0; subst hvv0
          exact ⟨v0', rfl, hvv⟩
      · next hc => rw [if_neg hc]; exact ihb hl
  | consDelta hb ih =>
      simp only [lookup] at hl ⊢; exact ih hl
  | consLambda hb ih =>
      simp only [lookup] at hl ⊢; exact ih hl
  | _ => trivial

/-- Triangle, `congDispatch` case: case-split on the developed subject's shape; when it is a
formation, the redex (`null`/`stop`/`dot`) still fires because `parB_preserves` carries the
side condition to the reduct, and a formation holding `λ` and `Δ` collapses by `ddl`/`dd`. -/
theorem tri_dispatch {s s' : Term} {a : Attr}
    (h : Par s s') (ihs : Par s' (devel s)) :
    Par (.dispatch s' a) (devel (.dispatch s a)) := by
  cases s with
  | bot => cases h with | refl => exact .dd a
  | glob => exact .congDispatch ihs
  | xi => exact .congDispatch ihs
  | dispatch t b => exact .congDispatch ihs
  | app t b arg => exact .congDispatch ihs
  | form bs =>
      rw [devel_dispatch]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl, hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]
        rcases par_form_inv h with ⟨cs, rfl, hbc⟩ | ⟨rfl, _, _⟩
        · exact .ddl (by rw [← parB_hasLambda hbc]; exact hl) (by rw [← parB_hasDelta hbc]; exact hd)
        · exact .dd a
      · rw [if_neg hld]
        simp only [Bool.not_eq_true] at hld
        obtain ⟨cs, rfl, hbc⟩ := par_form_inv' h hld
        rw [devel_form, hld] at ihs
        simp only [Bool.false_eq_true, if_false] at ihs
        have hld' : (hasLambda cs && hasDelta cs) = false := by
          rw [← parB_hasLambda hbc, ← parB_hasDelta hbc]; exact hld
        obtain ⟨ds, hds, hcd⟩ := par_form_inv' ihs hld'
        injection hds with hds; subst hds
        simp only [develDispatch]
        match hb : lookup bs a with
        | .void => exact .null hcd (parB_lookup_void hbc hb)
        | .attached v =>
            have hdv : lookup (develB bs) a = .attached (devel v) := lookup_develB bs a v hb
            simp only [hdv]
            by_cases hnf : nf (devel v)
            · simp only [hnf, if_true]
              obtain ⟨w, hw⟩ := parB_lookup_attached hbc hb
              exact .dot hcd hw hdv hnf hld'
            · simp only [hnf, Bool.false_eq_true, if_false]
              exact .congDispatch ihs
        | .absent =>
            by_cases hr : a = .rho
            · subst hr; simp only [if_true]; exact .norho hcd (parB_lookup_absent hbc hb)
            simp only [hr, if_false]
            match hphi : lookup bs .phi with
            | .absent =>
                by_cases hl : hasLambda bs = true
                · simp only [hl, if_true]; exact .congDispatch ihs
                · simp only [Bool.not_eq_true] at hl
                  simp only [hl, Bool.false_eq_true, if_false]
                  exact .stop hcd (parB_lookup_absent hbc hb)
                    (parB_lookup_absent hbc hphi) (by rw [← parB_hasLambda hbc]; exact hl)
            | .void => exact .congDispatch ihs
            | .attached _ => exact .congDispatch ihs

/-- Triangle, `congApp` case on a formation subject: the redex
(`stay`/`over`/`skip`/`miss`/`copy`) fires via `parB_preserves`. -/
theorem tri_app_attr {bs cs : List Binding} {a : Attr} {arg arg' : Term}
    (hbc : ParB bs cs) (hcd : ParB cs (develB bs)) (iharg : Par arg' (devel arg)) :
    Par (.app (.form cs) a arg') (develAttr bs (develB bs) a (devel arg)) := by
  simp only [develAttr]
  match hb : lookup bs a with
  | .attached v =>
      obtain ⟨w, hw⟩ := parB_lookup_attached hbc hb
      by_cases hr : a = .rho
      · subst hr; simp only [if_true]; exact .stay hcd hw iharg
      · simp only [hr, if_false]; exact .over hcd hw hr iharg
  | .absent =>
      by_cases hr : a = .rho
      · subst hr; simp only [if_true]; exact .skip hcd (parB_lookup_absent hbc hb) iharg
      · simp only [hr, if_false]; exact .miss hcd (parB_lookup_absent hbc hb) hr iharg
  | .void =>
      by_cases hcp : xiFree (devel arg) && nf (devel arg)
      · obtain ⟨hxi, hnf⟩ := Bool.and_eq_true_iff.mp hcp
        simp only [hcp, if_true]
        exact .copy hcd (parB_lookup_void hbc hb) iharg hxi hnf
      · simp only [hcp, Bool.false_eq_true, if_false]
        exact .congApp (.congForm hcd) iharg

/-- Triangle, `congApp` case: case-split on the developed subject's shape; on a formation the
redex fires via `tri_app_attr`, and a formation holding `λ` and `Δ`
collapses by `dcl`/`dc`. -/
theorem tri_app {s s' arg arg' : Term} {a : Attr}
    (h : Par s s') (ihs : Par s' (devel s)) (iharg : Par arg' (devel arg)) :
    Par (.app s' a arg') (devel (.app s a arg)) := by
  cases s with
  | bot => cases h with | refl => exact .dc iharg
  | glob => exact .congApp ihs iharg
  | xi => exact .congApp ihs iharg
  | dispatch t b => exact .congApp ihs iharg
  | app t b c => exact .congApp ihs iharg
  | form bs =>
      rw [devel_attr bs a arg]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl, hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]
        rcases par_form_inv h with ⟨cs, rfl, hbc⟩ | ⟨rfl, _, _⟩
        · exact .dcl (by rw [← parB_hasLambda hbc]; exact hl) (by rw [← parB_hasDelta hbc]; exact hd)
        · exact .dc iharg
      · rw [if_neg hld]
        simp only [Bool.not_eq_true] at hld
        obtain ⟨cs, rfl, hbc⟩ := par_form_inv' h hld
        rw [devel_form, hld] at ihs
        simp only [Bool.false_eq_true, if_false] at ihs
        have hld' : (hasLambda cs && hasDelta cs) = false := by
          rw [← parB_hasLambda hbc, ← parB_hasDelta hbc]; exact hld
        obtain ⟨ds, hds, hcd⟩ := par_form_inv' ihs hld'
        injection hds with hds; subst hds
        exact tri_app_attr hbc hcd iharg

/-- An application on a formation by an attached slot has a root redex (`stay`/`over`). -/
theorem appNF_attached {bs : List Binding} {a : Attr} {e₁ : Term} (h : lookup bs a = .attached e₁)
    (arg : Term) : appNF (.form bs) a arg = false := by
  simp [appNF, h]

/-- An application on a formation by an absent slot has a root redex (`skip` or `miss`). -/
theorem appNF_absent {bs : List Binding} {a : Attr} (h : lookup bs a = .absent) (arg : Term) :
    appNF (.form bs) a arg = false := by
  simp [appNF, h]

/-- An application on a formation by a void slot with a `ξ`-free argument has a root redex
(`copy`). -/
theorem appNF_void {bs : List Binding} {a : Attr} {arg : Term} (h : lookup bs a = .void)
    (hx : xiFree arg = true) : appNF (.form bs) a arg = false := by
  simp [appNF, h, hx]

/-- A normal formation has normal bindings and does not hold both `λ` and `Δ`. -/
theorem nf_form {bs : List Binding} (h : nf (.form bs) = true) :
    nfB bs = true ∧ (hasLambda bs && hasDelta bs) = false := by
  simpa only [nf, Bool.and_eq_true, Bool.not_eq_true'] using h

/-- **Normal forms only `Par`-reduce to themselves** (`nf e → Par e e' → e' = e`). Proved by the
two-motive recursor (`motive₂` is the `ParB` companion); every redex constructor is *vacuous* under
`nf e` because `nf` of that redex shape is `false`, and the congruences close by the IHs. This is
the load-bearing fact for the `dot`/`copy` triangle cases. -/
theorem nf_par_eq {e e' : Term} (hnf : nf e = true) (h : Par e e') : e' = e := by
  revert hnf
  induction h using Par.rec
    (motive_2 := fun bs bs' _ => nfB bs = true → bs' = bs) with
  | refl e => intro _; rfl
  | dd a => intro hnf; simp [nf, dispatchNF] at hnf
  | dc he ihe => intro hnf; simp [nf, appNF] at hnf
  | null hb hl ihb => intro hnf; simp [nf, dispatchNF, hl] at hnf
  | «over» hb hl hne he ihb ihe => intro hnf; simp [nf, appNF_attached hl] at hnf
  | stop hb h1 h2 h3 ihb => intro hnf; simp [nf, dispatchNF, h1, h2, h3] at hnf
  | norho hb hl ihb => intro hnf; simp [nf, dispatchNF, hl] at hnf
  | miss hb hl hne he ihb ihe => intro hnf; simp [nf, appNF_absent hl] at hnf
  | stay hb hl he ihb ihe => intro hnf; simp [nf, appNF_attached hl] at hnf
  | skip hb hl he ihb ihe => intro hnf; simp [nf, appNF_absent hl] at hnf
  | dot hb hl0 hl1 hnfe hld ihb => intro hnf; simp [nf, dispatchNF, hl0] at hnf
  | copy hb hl harg hxi hnfe ihb ihe =>
      intro hnf
      simp only [nf, Bool.and_eq_true] at hnf
      obtain ⟨⟨_, hna⟩, hap⟩ := hnf
      have hee := ihe hna
      subst hee
      rw [appNF_void hl hxi] at hap
      exact absurd hap (by simp)
  | dl hl hd => intro hnf; simp [nf, hl, hd] at hnf
  | ddl hl hd => intro hnf; simp [nf, hl, hd] at hnf
  | dcl hl hd => intro hnf; simp [nf, hl, hd] at hnf
  | congDispatch he ihe =>
      intro hnf
      simp only [nf, Bool.and_eq_true] at hnf
      have hee := ihe hnf.1
      subst hee; rfl
  | congApp he harg ihe iharg =>
      intro hnf
      simp only [nf, Bool.and_eq_true] at hnf
      obtain ⟨⟨hne, hnarg⟩, _⟩ := hnf
      have hee := ihe hne
      have haa := iharg hnarg
      subst hee; subst haa; rfl
  | congForm hb ihb =>
      intro hnf
      have := ihb (nf_form hnf).1
      subst this; rfl
  | nil => rfl
  | consVoid hb ihb =>
      rename_i hnf
      simp only [nfB] at hnf
      have := ihb hnf
      subst this; rfl
  | consAttached hv hb ihv ihb =>
      rename_i hnf
      simp only [nfB, Bool.and_eq_true] at hnf
      have hvv := ihv hnf.1
      have hbb := ihb hnf.2
      subst hvv; subst hbb; rfl
  | consDelta hb ihb =>
      rename_i hnf
      simp only [nfB] at hnf
      have := ihb hnf
      subst this; rfl
  | consLambda hb ihb =>
      rename_i hnf
      simp only [nfB] at hnf
      have := ihb hnf
      subst this; rfl

/-- **The complete development fixes a normal form** (`nf e → devel e = e`): if no rule fires
anywhere, `devel` rewrites nothing. By the `Term` recursor (`motive₃` the binding-list leg). -/
theorem nf_devel {e : Term} (hnf : nf e = true) : devel e = e := by
  induction e using Term.rec
    (motive_2 := fun b => ∀ a v, b = Binding.attached a v → nf v = true → devel v = v)
    (motive_3 := fun bs => nfB bs = true → develB bs = bs) with
  | bot => rfl
  | glob => rfl
  | xi => rfl
  | form bs ih =>
      obtain ⟨hb, hld⟩ := nf_form hnf
      simp only [devel_form, hld, ih hb, Bool.false_eq_true, if_false]
  | dispatch e a ihe =>
      simp only [nf, Bool.and_eq_true] at hnf
      obtain ⟨hne, hdisp⟩ := hnf
      cases e with
      | bot => simp [dispatchNF] at hdisp
      | glob => rfl
      | xi => rfl
      | dispatch s b => simp only [devel, ihe hne]
      | app s b arg => simp only [devel, ihe hne]
      | form bs =>
          have hdf := ihe hne
          obtain ⟨_, hld⟩ := nf_form hne
          simp only [devel_form, hld, Bool.false_eq_true, if_false] at hdf
          injection hdf with hb
          simp only [devel_dispatch, hld, Bool.false_eq_true, if_false, develDispatch]
          cases hl : lookup bs a with
          | void => simp [dispatchNF, hl] at hdisp
          | attached v => simp [dispatchNF, hl] at hdisp
          | absent =>
              by_cases hr : a = .rho
              · subst hr; simp [dispatchNF, hl] at hdisp
              simp only [hr, if_false]
              cases hphi : lookup bs .phi with
              | absent =>
                  simp only [dispatchNF, hl, hphi, hr, if_false] at hdisp
                  simp only [hdisp, hb, if_true]
              | void => simp only [hb]
              | attached v => simp only [hb]
  | app e a arg ihe iharg =>
      simp only [nf, Bool.and_eq_true] at hnf
      obtain ⟨⟨hne, hnarg⟩, happ⟩ := hnf
      cases e with
      | bot => simp [appNF] at happ
      | glob => simp only [devel, iharg hnarg]
      | xi => simp only [devel, iharg hnarg]
      | dispatch s b => simp only [devel, ihe hne, iharg hnarg]
      | app s b c => simp only [devel, ihe hne, iharg hnarg]
      | form bs =>
          have hdf := ihe hne
          obtain ⟨_, hld⟩ := nf_form hne
          simp only [devel_form, hld, Bool.false_eq_true, if_false] at hdf
          injection hdf with hb
          cases hl : lookup bs a with
          | attached v => rw [appNF_attached hl] at happ; exact absurd happ (by simp)
          | absent => rw [appNF_absent hl] at happ; exact absurd happ (by simp)
          | void =>
              have hda : devel arg = arg := iharg hnarg
              simp only [appNF, hl, Bool.not_eq_true'] at happ
              simp only [devel_attr bs a, hld, Bool.false_eq_true, if_false, develAttr, hl, hda,
                happ, Bool.false_and, hb]
  | nil => rfl
  | cons b r ihb ihr =>
      rename_i hnf
      cases b with
      | void a => simp only [nfB] at hnf; simp only [develB, ihr hnf]
      | attached a v =>
          simp only [nfB, Bool.and_eq_true] at hnf
          simp only [develB, ihb a v rfl hnf.1, ihr hnf.2]
      | delta d => simp only [nfB] at hnf; simp only [develB, ihr hnf]
      | lambda f => simp only [nfB] at hnf; simp only [develB, ihr hnf]
  | void a => rename_i hb _; nomatch hb
  | attached a v ihv =>
      rename_i hb hnfv; injection hb with _ hvv; subst hvv; exact ihv hnfv
  | delta d => rename_i hb _; nomatch hb
  | lambda f => rename_i hb _; nomatch hb

/-- **`C` is the identity on `ξ`-free terms** — if `e` has no spine `ξ` (`xiFree e`), then
`C(e ⊳ ctx) = e` for *every* context `ctx`. Contextualization only rewrites `ξ`-leaves (`Φ`,
formations and `⊥` are fixed; dispatch/app recurse into spine positions), so a term with no spine
`ξ` is untouched. This is the **fidelity bridge for `copy`**: the paper's `copy` places
`C(e₁ ⊳ scope)` in the filled slot whereas `Step.copy` places `e₁` directly — and under
`Step.copy`'s `xiFree e₁` guard these coincide for *any* `scope`, so dropping `scope`/`contextualize`
from `copy` is exact, not a weakening (README difference #7). Structural induction on `e`; the `ξ` case is
excluded by the hypothesis. -/
theorem contextualize_eq_self : ∀ {e : Term}, xiFree e = true → ∀ ctx, contextualize e ctx = e
  | .glob,        _, _   => rfl
  | .bot,         _, _   => rfl
  | .form _,      _, _   => rfl
  | .xi,          h, _   => by simp [xiFree] at h
  | .dispatch s _, h, ctx => by
      simp only [xiFree] at h
      simp only [contextualize, contextualize_eq_self h ctx]
  | .app s _ arg, h, ctx => by
      simp only [xiFree, Bool.and_eq_true] at h
      simp only [contextualize, contextualize_eq_self h.1 ctx, contextualize_eq_self h.2 ctx]

/-- **`C` commutes with `⇒` in the context argument** (`Par b b' → Par (C(e ⊳ b)) (C(e ⊳ b'))`).
Contextualization only inserts the context `b` at the `ξ`-leaves of `e` (and stops at formation
boundaries), so reducing `b` reduces every inserted copy in lockstep. Structural induction on `e`.
This is what the `dot`/`copy` triangle cases need: there the contextualized *expression* is the
already-normal `nf` value (fixed), and only the *context* — the developed receiver formation —
reduces (`form bs' ⇒ form (develB bs)`). -/
theorem par_contextualize_ctx {b b' : Term} (h : Par b b') :
    ∀ (e : Term), Par (contextualize e b) (contextualize e b')
  | .bot => .refl _
  | .glob => .refl _
  | .xi => h
  | .form _ => .refl _
  | .dispatch s _ => .congDispatch (par_contextualize_ctx h s)
  | .app s _ arg => .congApp (par_contextualize_ctx h s) (par_contextualize_ctx h arg)

/-- A well-formed application on a formation has well-formed bindings and a well-formed
argument. -/
theorem wf_app_form {bs : List Binding} {a : Attr} {e : Term} (h : WF (.app (.form bs) a e)) :
    WFB bs ∧ WF e := by
  cases h with | app hf harg => cases hf with | form _ hb => exact ⟨hb, harg⟩

/-- A well-formed dispatch on a formation has well-formed bindings. -/
theorem wf_dispatch_form {bs : List Binding} {a : Attr} (h : WF (.dispatch (.form bs) a)) :
    WFB bs := by
  cases h with | dispatch hf => cases hf with | form _ hb => exact hb

/-- **The Takahashi strict triangle**, stated for well-formed terms: any single `⇒`-step out of a well-formed
`e` is followed by a `⇒`-step into the complete development `devel e`. Proved by the
two-motive recursor whose motives **carry** the `WF`/`WFB` hypothesis; `motive_1` is *inferred*
from the reverted goal. This drives the `Abstract.Diamond ParWF` and the headline `confluence`. -/
theorem par_triangle {e u : Term} (hwf : WF e) (h : Par e u) : Par u (devel e) := by
  revert hwf
  induction h using Par.rec
    (motive_2 := fun bs bs' _ => WFB bs → ParB bs' (develB bs)) with
  | refl e => intro _; exact par_devel e
  | dd a => intro _; exact .refl _
  | dc he ihe => intro _; exact .refl _
  | null hb hl ihb =>
      intro _
      rw [devel_dispatch]
      simp only [develDispatch, hl, ite_self]
      exact .refl _
  | «over» hb hl hne he ihb ihe =>
      rename_i bs bs' a e₁ e₂ e₂'
      intro _
      rw [devel_attr bs a]; simp [develAttr, hl, hne]; exact .refl _
  | stop hb h1 h2 h3 ihb =>
      intro _
      rw [devel_dispatch]
      simp only [develDispatch, h1, h2, h3, Bool.false_and, Bool.false_eq_true, if_false, ite_self]
      exact .refl _
  | norho hb hl ihb =>
      intro _
      rw [devel_dispatch]
      simp [develDispatch, hl]
      exact .refl _
  | miss hb hl hne he ihb ihe =>
      intro _
      rw [devel_attr]
      simp only [develAttr, hl, hne, if_false, ite_self]
      exact .refl _
  | stay hb hl he ihb ihe =>
      rename_i bs bs' e₁ e₂ e₂'
      intro hwfa
      rw [devel_attr bs _]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl', hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]; exact par_dl hb hl' hd
      · rw [if_neg hld]
        simp only [develAttr, hl, if_true]
        exact .congForm (ihb (wf_app_form hwfa).1)
  | skip hb hl he ihb ihe =>
      rename_i bs bs' e₂ e₂'
      intro hwfa
      rw [devel_attr bs _]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl', hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]; exact par_dl hb hl' hd
      · rw [if_neg hld]
        simp only [develAttr, hl, if_true]
        exact .congForm (ihb (wf_app_form hwfa).1)
  | dot hb hl0 hl1 hnfe hld ihb =>
      rename_i bs bs' a e₀ e₁
      intro hwfd
      have hbd : ParB bs' (develB bs) := ihb (wf_dispatch_form hwfd)
      obtain ⟨w, hlw, hpw⟩ := parB_lookup_attached_par hbd hl1
      have hwe : w = e₁ := nf_par_eq hnfe hpw
      subst hwe
      rw [devel_dispatch]
      simp only [hld, Bool.false_eq_true, if_false, develDispatch, hl0, hlw, hnfe, if_true]
      exact .congApp (par_contextualize_ctx (.congForm (parB_erase hbd a)) w)
        (.congForm hbd)
  | copy hb hl harg hxi hnfe ihb ihe =>
      rename_i bs bs' a arg arg'
      intro hwfa
      obtain ⟨hwfb, hwfarg⟩ := wf_app_form hwfa
      rw [devel_attr bs a]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl', hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]
        exact .dl (by rw [hasLambda_fill, ← parB_hasLambda hb]; exact hl')
          (by rw [hasDelta_fill, ← parB_hasDelta hb]; exact hd)
      · rw [if_neg hld]
        have hda : devel arg = arg' := nf_par_eq hnfe (ihe hwfarg)
        simp only [develAttr, hl, hda, hxi, hnfe, Bool.and_self, if_true]
        exact .congForm (parB_fill (ihb hwfb) a arg')
  | dl hl hd =>
      intro _
      rw [devel_form]
      simp only [hl, hd, Bool.and_self, if_true]
      exact .refl _
  | ddl hl hd =>
      intro _
      rw [devel_dispatch]
      simp only [hl, hd, Bool.and_self, if_true]
      exact .refl _
  | dcl hl hd =>
      rename_i bs a e
      intro _
      rw [devel_attr bs a]; simp only [hl, hd, Bool.and_self, if_true]; exact .refl _
  | congDispatch he ihe =>
      intro hwfd
      cases hwfd with
      | dispatch hwfs => exact tri_dispatch he (ihe hwfs)
  | congApp he harg ihe iharg =>
      intro hwfa
      cases hwfa with
      | app hwfs hwfg => exact tri_app he (ihe hwfs) (iharg hwfg)
  | congForm hb ihb =>
      rename_i bs bs'
      intro hwff
      rw [devel_form]
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · obtain ⟨hl, hd⟩ := Bool.and_eq_true_iff.mp hld
        rw [if_pos hld]; exact par_dl hb hl hd
      · rw [if_neg hld]
        cases hwff with
        | form _ hwfb => exact .congForm (ihb hwfb)
  | nil => exact .nil
  | consVoid hb ihb =>
      rename_i hwfb
      exact .consVoid (ihb (by cases hwfb with | consVoid hr => exact hr))
  | consAttached hv hb ihv ihb =>
      rename_i hwfb
      exact .consAttached
        (ihv (by cases hwfb with | consAttached hvv _ => exact hvv))
        (ihb (by cases hwfb with | consAttached _ hr => exact hr))
  | consDelta hb ihb =>
      rename_i hwfb
      exact .consDelta (ihb (by cases hwfb with | consDelta hr => exact hr))
  | consLambda hb ihb =>
      rename_i hwfb
      exact .consLambda (ihb (by cases hwfb with | consLambda hr => exact hr))

/-! ## `nf` decides irreducibility (`nf_iff`)

The structural `nf` equals "no `Step` fires anywhere" — the faithful counterpart of phino's
`isNF`. Both directions hold for every term. `nf_iff` keeps its `WF` hypothesis only as
the scope the headline theorems share. -/

/-- A binding list with a non-`nf` attached value anywhere is not `nf` (`congForm` is a redex). -/
theorem nfB_set_false {bs₁ bs₂ : List Binding} {a : Attr} {e : Term}
    (h : nf e = false) : nfB (bs₁ ++ Binding.attached a e :: bs₂) = false := by
  induction bs₁ with
  | nil => simp only [List.nil_append, nfB, h, Bool.false_and]
  | cons b r ih =>
      cases b with
      | void c => simpa only [List.cons_append, nfB] using ih
      | attached c v =>
          simp only [List.cons_append, nfB, ih, Bool.and_false]
      | delta d => simpa only [List.cons_append, nfB] using ih
      | lambda f => simpa only [List.cons_append, nfB] using ih

/-- **Forward (unconditional): a reducible term is not `nf`.** Induction on the `Step` derivation;
each redex constructor falsifies the matching `dispatchNF`/`appNF` arm or the formation's `λ`/`Δ`
test, each congruence falsifies via the IH (and `nfB_set_false` for `congForm`). -/
theorem step_nf_false {e e' : Term} (h : e ↝ e') : nf e = false := by
  induction h with
  | dd a => simp [nf, dispatchNF]
  | dc a e => simp [nf, appNF]
  | null hv => simp [nf, dispatchNF, hv]
  | «over» hatt hne => simp [nf, appNF_attached hatt]
  | stop habs hphi hlam => simp [nf, dispatchNF, habs, hphi, hlam]
  | norho habs => simp [nf, dispatchNF, habs]
  | miss habs hne => simp [nf, appNF_absent habs]
  | stay hs => simp [nf, appNF_attached hs]
  | skip hs => simp [nf, appNF_absent hs]
  | dot hl hnfe hld => simp [nf, dispatchNF, hl]
  | copy hl hxi hnfe => simp [nf, appNF_void hl hxi]
  | dl hl hd => simp [nf, hl, hd]
  | congDispatch _ ih => simp [nf, ih]
  | congAppFn _ ih => simp [nf, ih]
  | congAppArg _ ih => simp [nf, ih]
  | congForm _ ih => simp only [nf, nfB_set_false ih, Bool.false_and]

/-- A non-`nf` binding list has an attached value that is not `nf`, exhibited by an append split. -/
theorem nfB_split_false {bs : List Binding} (h : nfB bs = false) :
    ∃ bs₁ a v bs₂, bs = bs₁ ++ Binding.attached a v :: bs₂ ∧ nf v = false := by
  induction bs with
  | nil => simp [nfB] at h
  | cons b r ih =>
      cases b with
      | void c =>
          simp only [nfB] at h
          obtain ⟨bs₁, a, v, bs₂, hbs, hnv⟩ := ih h
          exact ⟨Binding.void c :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hnv⟩
      | attached c w =>
          simp only [nfB, Bool.and_eq_false_iff] at h
          cases h with
          | inl hnw => exact ⟨[], c, w, r, rfl, hnw⟩
          | inr hr =>
              obtain ⟨bs₁, a, v, bs₂, hbs, hnv⟩ := ih hr
              exact ⟨Binding.attached c w :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hnv⟩
      | delta d =>
          simp only [nfB] at h
          obtain ⟨bs₁, a, v, bs₂, hbs, hnv⟩ := ih h
          exact ⟨Binding.delta d :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hnv⟩
      | lambda f =>
          simp only [nfB] at h
          obtain ⟨bs₁, a, v, bs₂, hbs, hnv⟩ := ih h
          exact ⟨Binding.lambda f :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hnv⟩

/-- In a `nf` binding list, an attached value found by `lookup` is itself `nf`. -/
theorem lookup_attached_nf {bs : List Binding} {a : Attr} {v : Term}
    (hnf : nfB bs = true) (hl : lookup bs a = .attached v) : nf v = true := by
  induction bs with
  | nil => simp [lookup] at hl
  | cons b r ih =>
      cases b with
      | void c =>
          simp only [lookup] at hl
          split at hl
          · nomatch hl
          · simp only [nfB] at hnf; exact ih hnf hl
      | attached c w =>
          simp only [nfB, Bool.and_eq_true] at hnf
          simp only [lookup] at hl
          split at hl
          · injection hl with hwv; subst hwv; exact hnf.1
          · exact ih hnf.2 hl
      | delta d =>
          simp only [lookup] at hl; simp only [nfB] at hnf; exact ih hnf hl
      | lambda f =>
          simp only [lookup] at hl; simp only [nfB] at hnf; exact ih hnf hl

/-- An application on a formation with a root redex reduces at the root, given a normal argument (`stay`/`over` on an attached slot, `copy` on a void one, `skip`/`miss`
on an absent one). -/
theorem reducible_app_attr {bs : List Binding} {a : Attr} {arg : Term}
    (h : appNF (.form bs) a arg = false) (hnarg : nf arg = true) :
    Reducible (.app (.form bs) a arg) := by
  cases hl : lookup bs a with
  | attached v =>
      by_cases hrho : a = .rho
      · subst hrho; exact ⟨_, Step.stay hl⟩
      · exact ⟨_, Step.over hl hrho⟩
  | void =>
      have happ : appNF (.form bs) a arg = !xiFree arg := by
        simp [appNF, hl]
      rw [happ] at h
      exact ⟨_, Step.copy hl (by simpa using h) hnarg⟩
  | absent =>
      by_cases hrho : a = .rho
      · subst hrho; exact ⟨_, Step.skip hl⟩
      · exact ⟨_, Step.miss hl hrho⟩

/-- **Backward: a non-`nf` well-formed term is reducible.** By the `Term` recursor (`motive₃`
collects the binding-list split + the value's reduction). On a formation, reduce a binding value
or collapse by `dl`; on a dispatch/application, reduce the subject/argument first, else case the
formation's `lookup` and fire the head rule. -/
theorem nf_false_reducible {e : Term} (hwf : WF e) (h : nf e = false) : Reducible e := by
  induction e using Term.rec
    (motive_2 := fun b => ∀ a v, b = Binding.attached a v → WF v → nf v = false → Reducible v)
    (motive_3 := fun bs => WFB bs → nfB bs = false →
      ∃ bs₁ a v bs₂, bs = bs₁ ++ Binding.attached a v :: bs₂ ∧ Reducible v) with
  | bot => simp [nf] at h
  | glob => simp [nf] at h
  | xi => simp [nf] at h
  | form bs ihbs =>
      simp only [nf, Bool.and_eq_false_iff, Bool.not_eq_false', Bool.and_eq_true] at h
      rcases h with h | ⟨hl, hd⟩
      · have hwfb : WFB bs := by cases hwf with | form _ hb => exact hb
        obtain ⟨bs₁, a, v, bs₂, hbs, v', hv'⟩ := ihbs hwfb h
        subst hbs
        exact ⟨_, Step.congForm hv'⟩
      · exact ⟨_, Step.dl hl hd⟩
  | dispatch e a ihe =>
      by_cases hne : nf e = false
      · obtain ⟨e', he'⟩ := ihe (by cases hwf with | dispatch hs => exact hs) hne
        exact ⟨_, Step.congDispatch he'⟩
      · simp only [Bool.not_eq_false] at hne
        simp only [nf, hne, Bool.true_and] at h
        cases hwf with
        | dispatch hwfe =>
        cases hwfe with
        | bot => exact ⟨_, Step.dd a⟩
        | glob => simp [dispatchNF] at h
        | xi => simp [dispatchNF] at h
        | dispatch hs => simp [dispatchNF] at h
        | app hs hg => simp [dispatchNF] at h
        | @form bs hnd hwfb =>
            obtain ⟨hnb, hld⟩ := nf_form hne
            cases hl : lookup bs a with
            | void => exact ⟨_, Step.null hl⟩
            | attached v => exact ⟨_, Step.dot hl (lookup_attached_nf hnb hl) hld⟩
            | absent =>
                by_cases hr : a = .rho
                · subst hr; exact ⟨_, Step.norho hl⟩
                simp only [dispatchNF, hl, hr, if_false] at h
                cases hphi : lookup bs .phi with
                | absent =>
                    simp only [hphi] at h
                    exact ⟨_, Step.stop hl hphi h⟩
                | void => simp [hphi] at h
                | attached w => simp [hphi] at h
  | app e a arg ihe iharg =>
      by_cases hne : nf e = false
      · obtain ⟨e', he'⟩ := ihe (by cases hwf with | app hs _ => exact hs) hne
        exact ⟨_, Step.congAppFn he'⟩
      · by_cases hnarg : nf arg = false
        · obtain ⟨arg', harg'⟩ := iharg (by cases hwf with | app _ hg => exact hg) hnarg
          exact ⟨_, Step.congAppArg harg'⟩
        · simp only [Bool.not_eq_false] at hne hnarg
          simp only [nf, hne, hnarg, Bool.and_true, Bool.true_and] at h
          cases hwf with
          | app hwfe hwfarg =>
          cases hwfe with
          | bot => exact ⟨_, Step.dc a arg⟩
          | glob => simp [appNF] at h
          | xi => simp [appNF] at h
          | dispatch hs => simp [appNF] at h
          | app hs hg => simp [appNF] at h
          | @form bs hnd hwfb => exact reducible_app_attr h hnarg
  | nil => rename_i _ hb; simp [nfB] at hb
  | cons b r ihb ihr =>
      rename_i hwfb hb
      cases b with
      | void c =>
          simp only [nfB] at hb
          obtain ⟨bs₁, a, v, bs₂, hbs, hred⟩ :=
            ihr (by cases hwfb with | consVoid hr => exact hr) hb
          exact ⟨Binding.void c :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hred⟩
      | attached c w =>
          simp only [nfB, Bool.and_eq_false_iff] at hb
          cases hb with
          | inl hnw =>
              have hwfw : WF w := by cases hwfb with | consAttached hv _ => exact hv
              exact ⟨[], c, w, r, rfl, ihb c w rfl hwfw hnw⟩
          | inr hr =>
              obtain ⟨bs₁, a, v, bs₂, hbs, hred⟩ :=
                ihr (by cases hwfb with | consAttached _ hr => exact hr) hr
              exact ⟨Binding.attached c w :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hred⟩
      | delta d =>
          simp only [nfB] at hb
          obtain ⟨bs₁, a, v, bs₂, hbs, hred⟩ :=
            ihr (by cases hwfb with | consDelta hr => exact hr) hb
          exact ⟨Binding.delta d :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hred⟩
      | lambda f =>
          simp only [nfB] at hb
          obtain ⟨bs₁, a, v, bs₂, hbs, hred⟩ :=
            ihr (by cases hwfb with | consLambda hr => exact hr) hb
          exact ⟨Binding.lambda f :: bs₁, a, v, bs₂, by rw [hbs]; rfl, hred⟩
  | void a => rename_i a' v hb _ _; nomatch hb
  | attached a v ihv =>
      rename_i a' v' hb hwfv hnv; injection hb with _ hvv; subst hvv; exact ihv hwfv hnv
  | delta d => rename_i a' v hb _ _; nomatch hb
  | lambda f => rename_i a' v hb _ _; nomatch hb

/-- **`nf` decides irreducibility on well-formed terms** (`WF e → (nf e ↔ NormalForm e)`): the
faithful counterpart of phino's `isNF`. -/
theorem nf_iff {e : Term} (hwf : WF e) : nf e = true ↔ NormalForm e := by
  constructor
  · intro hnf ⟨e', hstep⟩
    rw [step_nf_false hstep] at hnf
    exact absurd hnf (by simp)
  · intro hnorm
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    exact hnorm (nf_false_reducible hwf hne)

end PhiConfluence
