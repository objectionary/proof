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
via `Relation.church_rosser`; see `docs/DESIGN.md` §6 (proof architecture).

`Par` and `ParB` are **mutually inductive** (`ParB` reduces a binding list pointwise),
with a *bespoke cons-structured* `ParB` — the `List.Forall₂ ParBind` alternative is
kernel-rejected as a nested inductive carrying `Par`. The append index of `Step.congForm`
is crossed exactly once, by `parB_set`.

This module defines `Par`/`ParB` for the **rules currently in `Step`** (the `⊥`-collapse
six + `stay` + `phi` + `alpha` + congruence), connects the two relations (`step_to_par`,
`par_to_red`, the headline `redMany_eq` : `ReflTransGen Step = ReflTransGen Par`), and builds
the **Takahashi triangle**: the total complete development `devel`/`develB`, `par_devel`
(`e ⇒ devel e`), the `ParB` inversions (`parB_preserves`/`parB_lookup_*`/`parB_get_void`,
`par_form_inv`, `tri_dispatch`/`tri_app`), the `WF`-consuming `lookup_alpha_absent_of_wf`, and
`par_triangle` (now **`WF`-scoped**: `WF e → Par e u → Par u (devel e)`, since `alpha` makes the
unconditional triangle false — dev. #8). The triangle feeds `Diamond.lean`'s `parWF_diamond`
and, via `redMany_eq`, `Confluence.lean`'s headline `confluence`. The `nf`-guarded `dot`/`copy`
join both relations later (they need the `nf` guard, and then `devel` must guard on the
*developed* subterm).

Note: the discard constructors (`dc`/`null`/`over`/`stop`/`miss`) carry premises
(`ParB bs bs'`, `Par e e'`) that are unused in their `⊥` result, and `stay` carries an
unused argument-`Par` (only its `ParB`, used to build `form bs'`, matters). This is the
standard parallel-reduction shape — a single `⇒` step may develop subterms even while
collapsing — and `step_to_par`/`par_to_red`/the triangle simply discharge or discard
them; harmless, could be slimmed.
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
  | miss {bs bs' : List Binding} {a : Attr} {e e' : Term} :
      ParB bs bs' → lookup bs a = .absent → a.isAlpha = false → Par e e' →
      Par (.app (.form bs) a e) .bot
  | stay {bs bs' : List Binding} {e₁ e₂ e₂' : Term} :
      ParB bs bs' → lookup bs .rho = .attached e₁ → Par e₂ e₂' →
      Par (.app (.form bs) .rho e₂) (.form bs')
  | phi {bs bs' : List Binding} {a : Attr} :
      ParB bs bs' → lookup bs .phi ≠ .absent → lookup bs a = .absent →
      Par (.dispatch (.form bs) a) (.dispatch (.dispatch (.form bs') .phi) a)
  | alpha {bs bs' : List Binding} {i : Nat} {τ1 : Attr} {e e' : Term} :
      ParB bs bs' → voidAtOrdinal bs i = some τ1 → Par e e' →
      Par (.app (.form bs) (.alpha i) e) (.app (.form bs') τ1 e')
  | dot {bs bs' : List Binding} {a : Attr} {e₀ e₁ : Term} :
      ParB bs bs' → lookup bs a = .attached e₀ → lookup bs' a = .attached e₁ → nf e₁ = true →
      Par (.dispatch (.form bs) a) (.app (contextualize e₁ (.form bs')) .rho (.form bs'))
  | copy {bs bs' : List Binding} {a : Attr} {arg arg' : Term} :
      ParB bs bs' → lookup bs a = .void → Par arg arg' → xiFree arg' = true → nf arg' = true →
      Par (.app (.form bs) a arg) (.form (fill bs' a arg'))
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
  | refl => trivial
  | dd => trivial
  | dc => trivial
  | null => trivial
  | «over» => trivial
  | stop => trivial
  | miss => trivial
  | stay => trivial
  | phi => trivial
  | alpha => trivial
  | dot => trivial
  | copy => trivial
  | congDispatch => trivial
  | congApp => trivial
  | congForm => trivial
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
`hasLambda` flag: it reduces values, never keys, presence, or the `λ`-asset flag. The
engine behind the triangle's side-condition transport (a redex's guard still holds on the
developed binding list). -/
theorem parB_preserves {bs bs' : List Binding} (h : ParB bs bs') :
    (∀ a, lookup bs a = .void → lookup bs' a = .void)
      ∧ (∀ a, lookup bs a = .absent → lookup bs' a = .absent)
      ∧ (∀ a v, lookup bs a = .attached v → ∃ w, lookup bs' a = .attached w)
      ∧ hasLambda bs = hasLambda bs' := by
  induction h using ParB.rec (motive_1 := fun _ _ _ => True) with
  | refl => trivial
  | dd => trivial
  | dc => trivial
  | null => trivial
  | «over» => trivial
  | stop => trivial
  | miss => trivial
  | stay => trivial
  | phi => trivial
  | alpha => trivial
  | dot => trivial
  | copy => trivial
  | congDispatch => trivial
  | congApp => trivial
  | congForm => trivial
  | nil => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [lookup, hasLambda]
  | consVoid hb ih =>
      obtain ⟨iv, ia, iat, ih⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · next hc => rw [if_pos hc]
        · next hc => rw [if_neg hc]; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact iat a v ha
      · simp only [hasLambda]; exact ih
  | consAttached hvv hb _ ih =>
      obtain ⟨iv, ia, iat, ih⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; split at ha
        · nomatch ha
        · next hc => rw [if_neg hc]; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; split at ha
        · next hc => rw [if_pos hc]; exact ⟨_, rfl⟩
        · next hc => rw [if_neg hc]; exact iat a v ha
      · simp only [hasLambda]; exact ih
  | consDelta hb ih =>
      obtain ⟨iv, ia, iat, ih⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; exact iat a v ha
      · simp only [hasLambda]; exact ih
  | consLambda hb ih =>
      obtain ⟨iv, ia, iat, ih⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [lookup] at ha ⊢; exact iv a ha
      · intro a ha; simp only [lookup] at ha ⊢; exact ia a ha
      · intro a v ha; simp only [lookup] at ha ⊢; exact iat a v ha
      · simp only [hasLambda]

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
    hasLambda bs = hasLambda bs' := (parB_preserves h).2.2.2

/-- Every single step is a parallel step (`Step ⊆ Par`). -/
theorem step_to_par {e e' : Term} (h : e ↝ e') : Par e e' := by
  induction h with
  | dd a => exact .dd a
  | dc a e => exact .dc (.refl e)
  | null hv => exact .null (ParB.refl' _) hv
  | «over» hatt hne => exact .over (ParB.refl' _) hatt hne (.refl _)
  | stop habs hphi hlam => exact .stop (ParB.refl' _) habs hphi hlam
  | miss habs hna => exact .miss (ParB.refl' _) habs hna (.refl _)
  | stay hs => exact .stay (ParB.refl' _) hs (.refl _)
  | phi hpres habs => exact .phi (ParB.refl' _) hpres habs
  | alpha hget => exact .alpha (ParB.refl' _) hget (.refl _)
  | dot hl hnf => exact .dot (ParB.refl' _) hl hl hnf
  | copy hl hxi hnf => exact .copy (ParB.refl' _) hl (.refl _) hxi hnf
  | congDispatch _ ih => exact .congDispatch ih
  | congAppFn _ ih => exact .congApp ih (.refl _)
  | congAppArg _ ih => exact .congApp (.refl _) ih
  | congForm _ ih => exact .congForm (parB_set ih)

/-- A single step between formations lifts by prepending a binding (it is a `congForm`
on the extended prefix). -/
theorem step_form_cons {bs bs' : List Binding} (b : Binding) (h : Step (.form bs) (.form bs')) :
    Step (.form (b :: bs)) (.form (b :: bs')) := by
  obtain ⟨cs₁, c, f, f', cs₂, hbs, hbs', hf⟩ := form_step_inv h
  subst hbs
  injection hbs' with hbs'
  subst hbs'
  exact Step.congForm (bs₁ := b :: cs₁) hf

/-- Anything reachable from a formation is itself a formation (every step from a `form`
is a `congForm`). -/
theorem redMany_form_target {bs : List Binding} {t : Term} (h : (Term.form bs) ↝∗ t) :
    ∃ cs, t = .form cs := by
  induction h with
  | refl => exact ⟨bs, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨cs, rfl⟩ := ih
      obtain ⟨_, _, _, _, _, _, ht, _⟩ := form_step_inv hstep
      exact ⟨_, ht⟩

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
      obtain ⟨cs, hc⟩ := redMany_form_target h1
      subst hc
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
  | miss hb hl hna he ihb ihe => exact .single (Step.miss hl hna)
  | stay hb hl he ihb ihe => exact .head (Step.stay hl) ihb
  | phi hb hpres habs ihb =>
      exact .head (Step.phi hpres habs)
        (redMany_congDispatch _ (redMany_congDispatch Attr.phi ihb))
  | alpha hb hget he ihb ihe =>
      exact .head (Step.alpha hget)
        ((redMany_congAppFn _ _ ihb).trans (redMany_congAppArg _ _ ihe))
  | dot hb hl0 hl1 hnf ihb =>
      exact (redMany_congDispatch _ ihb).tail (Step.dot hl1 hnf)
  | copy hb hl harg hxi hnf ihb iharg =>
      exact ((redMany_congAppFn _ _ ihb).trans (redMany_congAppArg _ _ iharg)).tail
        (Step.copy (parB_lookup_void hb hl) hxi hnf)
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

/-- **First M3 headline:** single-step and parallel reduction have the *same*
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

mutual

/-- **Complete development** (Takahashi's `e*`): contract *every* redex present in `e` in one
sweep. It is the apex of the `Par`-diamond — `par_triangle` shows any single `⇒` out of a
well-formed `e` is itself followed by a `⇒` into `devel e`, so `d := devel a` joins any fork.
The `alpha` arm renames a positional `αᵢ` to the domain-ordinal-`i` void slot's key (`voidAtOrdinal`) but does
NOT fire the `copy`/`over` redex it creates — a single development contracts redexes *present*,
not created ones. `dot`/`copy` (M4.3/4.4) will need the guard-on-developed-subterm treatment.
Pattern order is load-bearing (the `.bot`-subject and `.form`-subject cases precede the
catch-alls), and `devel`'s side-condition matches mirror the `Par` constructors' guards exactly
so the triangle's `simp only [devel, …]` lines unfold cleanly. -/
def devel : Term → Term
  | .bot => .bot
  | .glob => .glob
  | .xi => .xi
  | .form bs => .form (develB bs)
  | .dispatch .bot _ => .bot
  | .dispatch (.form bs) a =>
      match lookup bs a with
      | .void => .bot
      | .attached _ =>
          match lookup (develB bs) a with
          | .attached e₁d =>
              if nf e₁d then .app (contextualize e₁d (.form (develB bs))) .rho (.form (develB bs))
              else .dispatch (.form (develB bs)) a
          | _ => .dispatch (.form (develB bs)) a
      | .absent =>
          match lookup bs .phi with
          | .absent =>
              match hasLambda bs with
              | false => .bot
              | true => .dispatch (.form (develB bs)) a
          | _ => .dispatch (.dispatch (.form (develB bs)) .phi) a
  | .dispatch e a => .dispatch (devel e) a
  | .app .bot _ _ => .bot
  | .app (.form bs) a e₂ =>
      match lookup bs a, decide (a = .rho) with
      | .attached _, true => .form (develB bs)
      | .attached _, false => .bot
      | .absent, _ =>
          match a with
          | .alpha i =>
              match voidAtOrdinal bs i with
              | some τ1 => .app (.form (develB bs)) τ1 (devel e₂)
              | none => .app (.form (develB bs)) a (devel e₂)
          | _ => .bot
      | .void, _ =>
          if xiFree (devel e₂) && nf (devel e₂) then .form (fill (develB bs) a (devel e₂))
          else .app (.form (develB bs)) a (devel e₂)
  | .app e a e₂ => .app (devel e) a (devel e₂)

/-- Complete development of a binding list (develop every attached value, keys/shape fixed). -/
def develB : List Binding → List Binding
  | [] => []
  | .void a :: rest => .void a :: develB rest
  | .attached a v :: rest => .attached a (devel v) :: develB rest
  | .delta d :: rest => .delta d :: develB rest
  | .lambda f :: rest => .lambda f :: develB rest
end

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

mutual

/-- `e ⇒ devel e`: every term parallel-reduces to its own complete development (the
reflexive apex of the triangle; reused by the congruence helpers). -/
theorem par_devel : ∀ (e : Term), Par e (devel e)
  | .bot => .refl _
  | .glob => .refl _
  | .xi => .refl _
  | .form bs => .congForm (parB_develB bs)
  | .dispatch .bot a => .dd a
  | .dispatch (.form bs) a => by
      simp only [devel]
      match h : lookup bs a with
      | .void => exact .null (parB_develB bs) h
      | .attached v =>
          match hd : lookup (develB bs) a with
          | .attached e₁d =>
              by_cases hnf : nf e₁d
              · simp only [hnf, if_pos]
                exact .dot (parB_develB bs) h hd hnf
              · simp only [hnf, if_neg, Bool.false_eq_true, not_false_iff]
                exact .congDispatch (.congForm (parB_develB bs))
          | .void =>
              have : lookup (develB bs) a = .attached (devel v) := lookup_develB bs a v h
              rw [this] at hd; nomatch hd
          | .absent =>
              have : lookup (develB bs) a = .attached (devel v) := lookup_develB bs a v h
              rw [this] at hd; nomatch hd
      | .absent =>
          match hphi : lookup bs .phi with
          | .absent =>
              match hl : hasLambda bs with
              | false => exact .stop (parB_develB bs) h hphi hl
              | true => exact .congDispatch (.congForm (parB_develB bs))
          | .void => exact .phi (parB_develB bs) (by rw [hphi]; intro hc; nomatch hc) h
          | .attached v => exact .phi (parB_develB bs) (by rw [hphi]; intro hc; nomatch hc) h
  | .dispatch .glob a => .congDispatch (.refl _)
  | .dispatch .xi a => .congDispatch (.refl _)
  | .dispatch (.dispatch s b) a => .congDispatch (par_devel _)
  | .dispatch (.app s b arg) a => .congDispatch (par_devel _)
  | .app .bot a e₂ => .dc (par_devel e₂)
  | .app (.form bs) a e₂ => by
      simp only [devel]
      match h : lookup bs a, hr : decide (a = .rho) with
      | .attached v, true =>
          have : a = .rho := by simpa using hr
          subst this
          exact .stay (parB_develB bs) h (par_devel e₂)
      | .attached v, false =>
          have : a ≠ .rho := by simp at hr; exact hr
          exact .over (parB_develB bs) h this (par_devel e₂)
      | .absent, b =>
          cases a with
          | alpha i =>
              cases hget : voidAtOrdinal bs i with
              | none => simp only [hget]; exact .congApp (.congForm (parB_develB bs)) (par_devel e₂)
              | some τ1 => simp only [hget]; exact .alpha (parB_develB bs) hget (par_devel e₂)
          | phi => exact .miss (parB_develB bs) h rfl (par_devel e₂)
          | rho => exact .miss (parB_develB bs) h rfl (par_devel e₂)
          | label nm => exact .miss (parB_develB bs) h rfl (par_devel e₂)
      | .void, b =>
          by_cases hcp : xiFree (devel e₂) && nf (devel e₂)
          · obtain ⟨hxi, hnf⟩ := Bool.and_eq_true_iff.mp hcp
            simp only [hcp, if_pos]
            exact .copy (parB_develB bs) h (par_devel e₂) hxi hnf
          · simp only [hcp, if_neg, Bool.false_eq_true, not_false_iff]
            exact .congApp (.congForm (parB_develB bs)) (par_devel e₂)
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
  | refl => trivial
  | dd => trivial
  | dc => trivial
  | null => trivial
  | «over» => trivial
  | stop => trivial
  | miss => trivial
  | stay => trivial
  | phi => trivial
  | alpha => trivial
  | dot => trivial
  | copy => trivial
  | congDispatch => trivial
  | congApp => trivial
  | congForm => trivial
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
      rename_i d _ _
      simp only [lookup] at hl ⊢; exact ih hl
  | consLambda hb ih =>
      rename_i f _ _
      simp only [lookup] at hl ⊢; exact ih hl

/-- A `Par`-reduct of a formation is a formation (the `Par`-level analogue of
`form_step_inv`; `Par` from a `form` is `refl` or `congForm`). -/
theorem par_form_inv {bs : List Binding} {t : Term} (h : Par (.form bs) t) :
    ∃ cs, t = .form cs ∧ ParB bs cs := by
  cases h with
  | refl => exact ⟨bs, rfl, ParB.refl' bs⟩
  | congForm hpb => rename_i cs; exact ⟨cs, rfl, hpb⟩

/-- `ParB` keeps the `i`-th void binding a void binding with the same key (positional
preservation, the engine behind the triangle's `alpha` side-condition transport). -/
theorem parB_voidAtOrdinal {bs bs' : List Binding} (h : ParB bs bs') :
    ∀ i, voidAtOrdinal bs i = voidAtOrdinal bs' i := by
  induction h using ParB.rec (motive_1 := fun _ _ _ => True) with
  | refl => trivial
  | dd => trivial
  | dc => trivial
  | null => trivial
  | «over» => trivial
  | stop => trivial
  | miss => trivial
  | stay => trivial
  | phi => trivial
  | alpha => trivial
  | dot => trivial
  | copy => trivial
  | congDispatch => trivial
  | congApp => trivial
  | congForm => trivial
  | nil => intro i; rfl
  | consVoid _ ih => intro i; cases i with
      | zero => rfl
      | succ j => simp only [voidAtOrdinal]; exact ih j
  | consAttached _ _ _ ih => intro i; cases i with
      | zero => rfl
      | succ j => simp only [voidAtOrdinal]; exact ih j
  | consDelta _ ih => intro i; simp only [voidAtOrdinal]; exact ih i
  | consLambda _ ih => intro i; simp only [voidAtOrdinal]; exact ih i

/-- The key well-formedness lemma: in a formation whose every key is legal (not a positional
`αᵢ`), looking up a positional `αᵢ` is `absent` — otherwise `αᵢ` would be in the domain, but
`legalKey (alpha i) = false`, contradiction. THIS is where `WF` is consumed by the triangle. -/
theorem lookup_alpha_absent_of_wf {bs : List Binding} {i : Nat}
    (h : ∀ a ∈ domain bs, a.legalKey = true) : lookup bs (.alpha i) = .absent := by
  induction bs with
  | nil => rfl
  | cons b r ih =>
      cases b with
      | void a =>
          simp only [lookup]
          split
          · next hc =>
              subst hc
              have : (Attr.alpha i).legalKey = true := h (.alpha i) (by simp [domain, Binding.key?])
              simp [Attr.legalKey] at this
          · next hc =>
              exact ih (fun x hx => h x (by simp only [domain, Binding.key?]; exact List.mem_cons_of_mem _ hx))
      | attached a v =>
          simp only [lookup]
          split
          · next hc =>
              subst hc
              have : (Attr.alpha i).legalKey = true := h (.alpha i) (by simp [domain, Binding.key?])
              simp [Attr.legalKey] at this
          · next hc =>
              exact ih (fun x hx => h x (by simp only [domain, Binding.key?]; exact List.mem_cons_of_mem _ hx))
      | delta d =>
          simp only [lookup]
          exact ih (fun x hx => h x (by simp only [domain, Binding.key?]; exact hx))
      | lambda f =>
          simp only [lookup]
          exact ih (fun x hx => h x (by simp only [domain, Binding.key?]; exact hx))

/-- Triangle, `congDispatch` case: case-split on the developed subject's shape; when it is a
formation, the redex (`null`/`stop`/`phi`) still fires because `parB_preserves` carries the
side condition to the reduct. -/
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
      obtain ⟨cs, rfl, hbc⟩ := par_form_inv h
      obtain ⟨ds, hds, hcd⟩ := par_form_inv ihs
      simp only [devel] at hds ⊢
      injection hds with hds; subst hds
      match hb : lookup bs a with
      | .void => exact .null hcd (parB_lookup_void hbc hb)
      | .attached v =>
          match hd : lookup (develB bs) a with
          | .attached e₁d =>
              by_cases hnf : nf e₁d
              · simp only [hnf, if_pos]
                obtain ⟨w, hw⟩ := parB_lookup_attached hbc hb
                exact .dot hcd hw hd hnf
              · simp only [hnf, if_neg, Bool.false_eq_true, not_false_iff]
                exact .congDispatch ihs
          | .void =>
              have := lookup_develB bs a v hb
              rw [this] at hd; nomatch hd
          | .absent =>
              have := lookup_develB bs a v hb
              rw [this] at hd; nomatch hd
      | .absent =>
          match hphi : lookup bs .phi with
          | .absent =>
              match hl : hasLambda bs with
              | false =>
                  exact .stop hcd (parB_lookup_absent hbc hb)
                    (parB_lookup_absent hbc hphi) (by rw [← parB_hasLambda hbc]; exact hl)
              | true => exact .congDispatch ihs
          | .void =>
              exact .phi hcd (by rw [parB_lookup_void hbc hphi]; nofun) (parB_lookup_absent hbc hb)
          | .attached v =>
              obtain ⟨w, hw⟩ := parB_lookup_attached hbc hphi
              exact .phi hcd (by rw [hw]; nofun) (parB_lookup_absent hbc hb)

/-- Triangle, `congApp` case (now `WF`-aware): case-split on the developed subject's shape; on a
formation the redex (`stay`/`over`/`miss`/`alpha`) fires via `parB_preserves`. The extra
`hwf : WF s` parameter discharges the formation-`alpha` sub-case via `lookup_alpha_absent_of_wf`
(under `WF`, a positional `αᵢ` is never a key, so `devel` takes the positional `alpha` branch). -/
theorem tri_app {s s' arg arg' : Term} {a : Attr}
    (hwf : WF s) (h : Par s s') (ihs : Par s' (devel s)) (iharg : Par arg' (devel arg)) :
    Par (.app s' a arg') (devel (.app s a arg)) := by
  cases s with
  | bot => cases h with | refl => exact .dc iharg
  | glob => exact .congApp ihs iharg
  | xi => exact .congApp ihs iharg
  | dispatch t b => exact .congApp ihs iharg
  | app t b c => exact .congApp ihs iharg
  | form bs =>
      obtain ⟨cs, rfl, hbc⟩ := par_form_inv h
      obtain ⟨ds, hds, hcd⟩ := par_form_inv ihs
      simp only [devel] at hds ⊢
      injection hds with hds; subst hds
      cases hwf with
      | form _ _ _ =>
          match hb : lookup bs a, hr : decide (a = .rho) with
          | .attached v, true =>
              have hrr : a = .rho := by simpa using hr
              subst hrr
              obtain ⟨w, hw⟩ := parB_lookup_attached hbc hb
              exact .stay hcd hw iharg
          | .attached v, false =>
              have hrr : a ≠ .rho := by simp at hr; exact hr
              obtain ⟨w, hw⟩ := parB_lookup_attached hbc hb
              exact .over hcd hw hrr iharg
          | .absent, _ =>
              cases a with
              | alpha i =>
                  cases hget : voidAtOrdinal bs i with
                  | none => simp only [hget]; exact .congApp ihs iharg
                  | some τ1 => simp only [hget]; exact .alpha hcd (parB_voidAtOrdinal hbc i ▸ hget) iharg
              | phi => exact .miss hcd (parB_lookup_absent hbc hb) rfl iharg
              | rho => exact .miss hcd (parB_lookup_absent hbc hb) rfl iharg
              | label nm => exact .miss hcd (parB_lookup_absent hbc hb) rfl iharg
          | .void, _ =>
              by_cases hcp : xiFree (devel arg) && nf (devel arg)
              · obtain ⟨hxi, hnf⟩ := Bool.and_eq_true_iff.mp hcp
                simp only [hcp, if_pos]
                exact .copy hcd (parB_lookup_void hbc hb) iharg hxi hnf
              · simp only [hcp, if_neg, Bool.false_eq_true, not_false_iff]
                exact .congApp ihs iharg

/-- **Normal forms only `Par`-reduce to themselves** (`nf e → Par e e' → e' = e`). Proved by the
two-motive recursor (`motive₂` is the `ParB` companion); every redex constructor is *vacuous* under
`nf e` because `nf` of that redex shape is `false` (the eleven-rule `nf` already classifies
`dot`/`copy`/`alpha`/… redexes as reducible), and the congruences close by the IHs. This is the
load-bearing fact for the M4.3c/M4.4 `dot`/`copy` triangle cases (`nf e₁' → Par e₁ e₁' → devel e₁ =
e₁'`, combined with `par_triangle`). -/
theorem nf_par_eq {e e' : Term} (hnf : nf e = true) (h : Par e e') : e' = e := by
  revert hnf
  induction h using Par.rec
    (motive_2 := fun bs bs' _ => nfB bs = true → bs' = bs) with
  | refl e => intro _; rfl
  | dd a => intro hnf; simp [nf, dispatchNF] at hnf
  | dc he ihe => intro hnf; simp [nf, appNF] at hnf
  | null hb hl ihb => intro hnf; rename_i bs bs' a; simp [nf, dispatchNF, hl] at hnf
  | «over» hb hl hne he ihb ihe =>
      intro hnf; rename_i bs bs' a e₁ e₂ e₂'; simp [nf, appNF, hl] at hnf
  | stop hb h1 h2 h3 ihb =>
      intro hnf; rename_i bs bs' a; simp [nf, dispatchNF, h1, h2, h3] at hnf
  | miss hb hl hna he ihb ihe =>
      intro hnf; rename_i bs bs' a e e'
      cases a with
      | phi => simp [nf, appNF, hl] at hnf
      | rho => simp [nf, appNF, hl] at hnf
      | alpha i => simp [Attr.isAlpha] at hna
      | label nm => simp [nf, appNF, hl] at hnf
  | stay hb hl he ihb ihe =>
      intro hnf; rename_i bs bs' e₁ e₂ e₂'; simp [nf, appNF, hl] at hnf
  | phi hb hpres habs ihb =>
      intro hnf; rename_i bs bs' a
      cases hlphi : lookup bs .phi with
      | absent => exact absurd hlphi hpres
      | void => simp [nf, dispatchNF, habs, hlphi] at hnf
      | attached v => simp [nf, dispatchNF, habs, hlphi] at hnf
  | alpha hb hget he ihb ihe =>
      intro hnf; rename_i bs bs' i τ1 e e'
      simp only [nf, appNF, Bool.and_eq_true] at hnf
      obtain ⟨⟨_, _⟩, hap⟩ := hnf
      cases hl : lookup bs (.alpha i) with
      | attached v => rw [hl] at hap; simp at hap
      | void => rw [hl] at hap; simp at hap
      | absent => rw [hl] at hap; rw [hget] at hap; simp at hap
  | dot hb hl0 hl1 hnfe ihb =>
      intro hnf; rename_i bs bs' a e₀ e₁
      simp [nf, dispatchNF, hl0] at hnf
  | copy hb hl harg hxi hnfe ihb ihe =>
      intro hnf; rename_i bs bs' a arg arg'
      have hclose : nf arg = true ∧ xiFree arg = false := by
        cases a with
        | alpha i => simp [nf, appNF, hl] at hnf
        | phi =>
            simp only [nf, appNF, hl, Bool.and_eq_true, Bool.not_eq_true'] at hnf
            exact ⟨hnf.1.2, hnf.2⟩
        | rho =>
            simp only [nf, appNF, hl, Bool.and_eq_true, Bool.not_eq_true'] at hnf
            exact ⟨hnf.1.2, hnf.2⟩
        | label nm =>
            simp only [nf, appNF, hl, Bool.and_eq_true, Bool.not_eq_true'] at hnf
            exact ⟨hnf.1.2, hnf.2⟩
      have hee := ihe hclose.1
      subst hee
      rw [hxi] at hclose
      exact absurd hclose.2 (by simp)
  | congDispatch he ihe =>
      intro hnf; rename_i e e' a
      simp only [nf, Bool.and_eq_true] at hnf
      have hee := ihe hnf.1
      subst hee; rfl
  | congApp he harg ihe iharg =>
      intro hnf; rename_i e e' a arg arg'
      simp only [nf, Bool.and_eq_true] at hnf
      obtain ⟨⟨hne, hnarg⟩, _⟩ := hnf
      have hee := ihe hne
      have haa := iharg hnarg
      subst hee; subst haa; rfl
  | congForm hb ihb =>
      intro hnf; rename_i bs bs'
      simp only [nf] at hnf
      have := ihb hnf
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
anywhere, `devel` rewrites nothing. By the `Term` recursor (`motive₃` the binding-list leg). Used
with `nf_par_eq` to pin the `dot`/`copy` development at M4.3c/M4.4. -/
theorem nf_devel {e : Term} (hnf : nf e = true) : devel e = e := by
  induction e using Term.rec
    (motive_2 := fun b => ∀ a v, b = Binding.attached a v → nf v = true → devel v = v)
    (motive_3 := fun bs => nfB bs = true → develB bs = bs) with
  | bot => rfl
  | glob => rfl
  | xi => rfl
  | form bs ih =>
      simp only [nf] at hnf
      simp only [devel, ih hnf]
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
          simp only [nf] at hne
          cases hl : lookup bs a with
          | void => simp [dispatchNF, hl] at hdisp
          | attached v => simp [dispatchNF, hl] at hdisp
          | absent =>
              have hb : develB bs = bs := by
                have := ihe hne; simp only [devel] at this; injection this
              simp only [devel, hl]
              cases hphi : lookup bs .phi with
              | absent =>
                  simp only [dispatchNF, hl, hphi] at hdisp
                  simp only [hdisp, hb]
              | void => simp [dispatchNF, hl, hphi] at hdisp
              | attached v => simp [dispatchNF, hl, hphi] at hdisp
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
          simp only [nf] at hne
          have hb : develB bs = bs := by
            have := ihe hne; simp only [devel] at this; injection this
          cases hl : lookup bs a with
          | attached v => simp [appNF, hl] at happ
          | void =>
              have hda : devel arg = arg := iharg hnarg
              cases a with
              | alpha i => simp [appNF, hl] at happ
              | phi =>
                  simp only [appNF, hl, Bool.not_eq_true'] at happ
                  simp only [devel, hl, hda, happ, Bool.false_and, Bool.false_eq_true, if_false, hb]
              | rho =>
                  simp only [appNF, hl, Bool.not_eq_true'] at happ
                  simp only [devel, hl, hda, happ, Bool.false_and, Bool.false_eq_true, if_false, hb]
              | label nm =>
                  simp only [appNF, hl, Bool.not_eq_true'] at happ
                  simp only [devel, hl, hda, happ, Bool.false_and, Bool.false_eq_true, if_false, hb]
          | absent =>
              cases a with
              | alpha i =>
                  simp only [appNF, hl] at happ
                  cases hget : voidAtOrdinal bs i with
                  | none => simp only [devel, hl, hget, hb, iharg hnarg]
                  | some τ1 => rw [hget] at happ; simp at happ
              | phi => simp [appNF, hl] at happ
              | rho => simp [appNF, hl] at happ
              | label nm => simp [appNF, hl] at happ
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
from `copy` is exact, not a weakening (M0-spec dev. #7). Structural induction on `e`; the `ξ` case is
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

/-- **The Takahashi strict triangle**, now **WF-scoped**: any single `⇒`-step out of a
well-formed `e` is followed by a `⇒`-step into the complete development `devel e`. With the
`alpha` rule present this is no longer unconditional — the `alpha`-vs-`over` fork on malformed
`αᵢ`-keyed formations is non-joinable (dev. #8) — so `WF e` is load-bearing: the `alpha` case
consumes it via `lookup_alpha_absent_of_wf` to unfold `devel`. Proved by the two-motive recursor
whose motives **carry** the `WF`/`WFB` hypothesis; `motive_1` is *inferred* from the reverted goal
(supplying it explicitly conflicts with the eliminator's motive unification). This drives the
`Abstract.Diamond ParWF` and the headline `confluence`. -/
theorem par_triangle {e u : Term} (hwf : WF e) (h : Par e u) : Par u (devel e) := by
  revert hwf
  induction h using Par.rec
    (motive_2 := fun bs bs' _ => WFB bs → ParB bs' (develB bs)) with
  | refl e => intro _; exact par_devel e
  | dd a => intro _; exact .refl _
  | dc he ihe => intro _; exact .refl _
  | null hb hl ihb =>
      rename_i bs bs' a
      intro _
      show Par .bot (devel (.dispatch (.form bs) a))
      simp only [devel, hl]; exact .refl _
  | «over» hb hl hne he ihb ihe =>
      rename_i bs bs' a e₁ e₂ e₂'
      intro _
      show Par .bot (devel (.app (.form bs) a e₂))
      simp only [devel, hl, decide_eq_false hne]; exact .refl _
  | stop hb h1 h2 h3 ihb =>
      rename_i bs bs' a
      intro _
      show Par .bot (devel (.dispatch (.form bs) a))
      simp only [devel, h1, h2, h3]; exact .refl _
  | miss hb hl hna he ihb ihe =>
      rename_i bs bs' a e e'
      intro _
      show Par .bot (devel (.app (.form bs) a e))
      cases a with
      | phi => simp only [devel, hl]; exact .refl _
      | rho => simp only [devel, hl]; exact .refl _
      | alpha i => exact absurd hna (by simp [Attr.isAlpha])
      | label nm => simp only [devel, hl]; exact .refl _
  | stay hb hl he ihb ihe =>
      rename_i bs bs' e₁ e₂ e₂'
      intro hwfa
      show Par (.form bs') (devel (.app (.form bs) .rho e₂))
      have hwfb : WFB bs := by cases hwfa with | app hf _ => cases hf with | form _ _ hb' => exact hb'
      simp only [devel, hl]
      exact .congForm (ihb hwfb)
  | phi hb hpres habs ihb =>
      rename_i bs bs' a
      intro hwfd
      show Par (.dispatch (.dispatch (.form bs') .phi) a) (devel (.dispatch (.form bs) a))
      have hwfb : WFB bs := by cases hwfd with | dispatch hf => cases hf with | form _ _ hb' => exact hb'
      simp only [devel, habs]
      match hphi : lookup bs .phi with
      | .absent => exact absurd hphi hpres
      | .void => exact .congDispatch (.congDispatch (.congForm (ihb hwfb)))
      | .attached v => exact .congDispatch (.congDispatch (.congForm (ihb hwfb)))
  | alpha hb hget he ihb ihe =>
      rename_i bs bs' i τ1 e e'
      intro hwfa
      show Par (.app (.form bs') τ1 e') (devel (.app (.form bs) (.alpha i) e))
      have hwff : WF (.form bs) := by cases hwfa with | app hf _ => exact hf
      have hwfb : WFB bs := by cases hwff with | form _ _ hb' => exact hb'
      have hwfe : WF e := by cases hwfa with | app _ harg => exact harg
      have hleg : ∀ a ∈ domain bs, a.legalKey = true := by cases hwff with | form _ hl _ => exact hl
      have habs : lookup bs (.alpha i) = .absent := lookup_alpha_absent_of_wf hleg
      simp only [devel, habs, hget]
      exact .congApp (.congForm (ihb hwfb)) (ihe hwfe)
  | dot hb hl0 hl1 hnfe ihb =>
      rename_i bs bs' a e₀ e₁
      intro hwfd
      show Par (.app (contextualize e₁ (.form bs')) .rho (.form bs'))
        (devel (.dispatch (.form bs) a))
      have hwfb : WFB bs := by cases hwfd with | dispatch hf => cases hf with | form _ _ hb' => exact hb'
      have hbd : ParB bs' (develB bs) := ihb hwfb
      obtain ⟨w, hlw, hpw⟩ := parB_lookup_attached_par hbd hl1
      have hwe : w = e₁ := nf_par_eq hnfe hpw
      subst hwe
      simp only [devel, hl0, hlw, hnfe, if_true]
      exact .congApp (par_contextualize_ctx (.congForm hbd) w) (.congForm hbd)
  | copy hb hl harg hxi hnfe ihb ihe =>
      rename_i bs bs' a arg arg'
      intro hwfa
      show Par (.form (fill bs' a arg')) (devel (.app (.form bs) a arg))
      have hwff : WF (.form bs) := by cases hwfa with | app hf _ => exact hf
      have hwfb : WFB bs := by cases hwff with | form _ _ hb' => exact hb'
      have hwfarg : WF arg := by cases hwfa with | app _ harg => exact harg
      have hbd : ParB bs' (develB bs) := ihb hwfb
      have hpda : Par arg' (devel arg) := ihe hwfarg
      have hda : devel arg = arg' := nf_par_eq hnfe hpda
      simp only [devel, hl, hda, hxi, hnfe, Bool.and_self, if_true]
      exact .congForm (parB_fill hbd a arg')
  | congDispatch he ihe =>
      intro hwfd
      cases hwfd with
      | dispatch hwfs => exact tri_dispatch he (ihe hwfs)
  | congApp he harg ihe iharg =>
      intro hwfa
      cases hwfa with
      | app hwfs hwfg => exact tri_app hwfs he (ihe hwfs) (iharg hwfg)
  | congForm hb ihb =>
      intro hwff
      cases hwff with
      | form _ _ hwfb => exact .congForm (ihb hwfb)
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
`isNF`. Forward (`step_nf_false`) is unconditional; the converse needs **`WF`** (consumed exactly
once, via `lookup_alpha_absent_of_wf`): an `αᵢ`-keyed *void* slot is marked a redex by `appNF` but
the `alpha` rule fires by domain ordinal (`voidAtOrdinal`), so the malformed term `⟦αᵢ↦∅⟧(αᵢ↦e)` with a
non-`ξ`-free normal `e` has `nf = false` yet is irreducible — `WF` (legal-key invariant, dev. #8)
bars that key. -/

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
each redex constructor falsifies the matching `dispatchNF`/`appNF` arm, each congruence falsifies via
the IH (and `nfB_set_false` for `congForm`). -/
theorem step_nf_false {e e' : Term} (h : e ↝ e') : nf e = false := by
  induction h with
  | dd a => simp [nf, dispatchNF]
  | dc a e => simp [nf, appNF]
  | null hv => rename_i bs a; simp [nf, dispatchNF, hv]
  | «over» hatt hne => rename_i bs a e₁ e₂; simp [nf, appNF, hatt]
  | stop habs hphi hlam => rename_i bs a; simp [nf, dispatchNF, habs, hphi, hlam]
  | miss habs hna =>
      rename_i bs a e
      cases a with
      | phi => simp [nf, appNF, habs]
      | rho => simp [nf, appNF, habs]
      | alpha i => simp [Attr.isAlpha] at hna
      | label nm => simp [nf, appNF, habs]
  | stay hs => rename_i bs e₁ e₂; simp [nf, appNF, hs]
  | phi hpres habs =>
      rename_i bs a
      cases hlphi : lookup bs .phi with
      | absent => exact absurd hlphi hpres
      | void => simp [nf, dispatchNF, habs, hlphi]
      | attached v => simp [nf, dispatchNF, habs, hlphi]
  | alpha hget =>
      rename_i bs i τ₁ e
      simp only [nf, appNF, Bool.and_eq_false_iff]
      right
      cases hl : lookup bs (.alpha i) with
      | attached v => rfl
      | void => rfl
      | absent => rw [hget]
  | dot hl hnfe => rename_i bs a e₁; simp [nf, dispatchNF, hl]
  | copy hl hxi hnfe =>
      rename_i bs a e₁
      simp only [nf, appNF, hl]
      cases a with
      | alpha i => simp
      | phi => simp [hxi]
      | rho => simp [hxi]
      | label nm => simp [hxi]
  | congDispatch _ ih => rename_i e e' a; simp [nf, ih]
  | congAppFn _ ih => rename_i e e' a arg; simp [nf, ih]
  | congAppArg _ ih => rename_i e a arg arg'; simp [nf, ih]
  | congForm _ ih => rename_i bs₁ bs₂ a e e'; simpa only [nf] using nfB_set_false ih

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

/-- **Backward (`WF`-scoped): a non-`nf` well-formed term is reducible.** By the `Term` recursor
(`motive₃` collects the binding-list split + the value's reduction). On a dispatch/application,
reduce the subject/argument first; else case the formation's `lookup` and fire the head rule —
`WF` (via `lookup_alpha_absent_of_wf`) rules out the `αᵢ`-keyed `void`/`absent` slots that `appNF`
would otherwise flag without a matching `Step`. -/
theorem nf_false_reducible {e : Term} (hwf : WF e) (h : nf e = false) : Reducible e := by
  induction e using Term.rec
    (motive_2 := fun b => ∀ a v, b = Binding.attached a v → WF v → nf v = false → Reducible v)
    (motive_3 := fun bs => WFB bs → nfB bs = false →
      ∃ bs₁ a v bs₂, bs = bs₁ ++ Binding.attached a v :: bs₂ ∧ Reducible v) with
  | bot => simp [nf] at h
  | glob => simp [nf] at h
  | xi => simp [nf] at h
  | form bs ihbs =>
      simp only [nf] at h
      have hwfb : WFB bs := by cases hwf with | form _ _ hb => exact hb
      obtain ⟨bs₁, a, v, bs₂, hbs, v', hv'⟩ := ihbs hwfb h
      subst hbs
      exact ⟨_, Step.congForm hv'⟩
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
        | @form bs hnd hlegal hwfb =>
            cases hl : lookup bs a with
            | void => exact ⟨_, Step.null hl⟩
            | attached v =>
                refine ⟨_, Step.dot hl ?_⟩
                exact lookup_attached_nf (by simpa only [nf] using hne) hl
            | absent =>
                simp only [dispatchNF, hl] at h
                cases hphi : lookup bs .phi with
                | absent =>
                    simp only [hphi] at h
                    exact ⟨_, Step.stop hl hphi h⟩
                | void => exact ⟨_, Step.phi (by rw [hphi]; simp) hl⟩
                | attached w => exact ⟨_, Step.phi (by rw [hphi]; simp) hl⟩
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
          | @form bs hnd hlegal hwfb =>
              cases hl : lookup bs a with
              | attached v =>
                  by_cases hrho : a = .rho
                  · subst hrho; exact ⟨_, Step.stay hl⟩
                  · exact ⟨_, Step.over hl hrho⟩
              | void =>
                  cases a with
                  | alpha i =>
                      rw [lookup_alpha_absent_of_wf hlegal] at hl
                      exact absurd hl (by simp)
                  | phi =>
                      simp only [appNF, hl] at h
                      exact ⟨_, Step.copy hl (by simpa using h) hnarg⟩
                  | rho =>
                      simp only [appNF, hl] at h
                      exact ⟨_, Step.copy hl (by simpa using h) hnarg⟩
                  | label nm =>
                      simp only [appNF, hl] at h
                      exact ⟨_, Step.copy hl (by simpa using h) hnarg⟩
              | absent =>
                  cases a with
                  | alpha i =>
                      rw [lookup_alpha_absent_of_wf hlegal] at hl
                      simp only [appNF] at h
                      rw [lookup_alpha_absent_of_wf hlegal] at h
                      cases hget : voidAtOrdinal bs i with
                      | none => rw [hget] at h; simp at h
                      | some τ1 => exact ⟨_, Step.alpha hget⟩
                  | phi => exact ⟨_, Step.miss hl (by simp [Attr.isAlpha])⟩
                  | rho => exact ⟨_, Step.miss hl (by simp [Attr.isAlpha])⟩
                  | label nm => exact ⟨_, Step.miss hl (by simp [Attr.isAlpha])⟩
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
faithful counterpart of phino's `isNF`. (Unconditional `nf_iff` is *false* — see the docblock.) -/
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
