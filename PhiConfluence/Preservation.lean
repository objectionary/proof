-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Parallel
import PhiConfluence.WellFormed

/-!
# Preservation of well-formedness (M4.1)

The headline diamond and confluence theorems are stated for well-formed terms, so the
reduction relations must not break that invariant. This module proves that one `Step`
and one `Par` step both preserve `WF`, adding no new rules. The engine is
`domain_set`/`parB_domain`: neither relation touches a binding's key, so the `domain`
(hence `Nodup`/`legalKey`) is fixed, and only the attached values must be re-proved
well-formed — `wfb_set` for `Step.congForm`'s append index and `wf_form_of_parB` for the
`Par` formation cases. `WF.par`'s binding-list leg is handled inline by the recursor's
`motive₂` (no separate `ParB` companion — that would duplicate the case analysis, a sync
liability once `alpha`/`dot`/`copy` arrive).
-/

namespace PhiConfluence

/-- The attached value of a binding inside a well-formed binding list is well-formed:
peel the prefix `bs₁` one binding at a time until the target `attached a e` is exposed. -/
theorem wfb_attached_wf {bs₁ bs₂ : List Binding} {a : Attr} {e : Term}
    (h : WFB (bs₁ ++ .attached a e :: bs₂)) : WF e := by
  induction bs₁ with
  | nil => cases h with | consAttached hv _ => exact hv
  | cons b r ih =>
      cases b with
      | void c => cases h with | consVoid hr => exact ih hr
      | attached c v => cases h with | consAttached _ hr => exact ih hr
      | delta d => cases h with | consDelta hr => exact ih hr
      | lambda f => cases h with | consLambda hr => exact ih hr

/-- Replacing the attached value at one position by another well-formed term preserves
well-formedness of the whole binding list (the other bindings are untouched). -/
theorem wfb_set {bs₁ bs₂ : List Binding} {a : Attr} {e e' : Term}
    (h : WFB (bs₁ ++ .attached a e :: bs₂)) (he : WF e') :
    WFB (bs₁ ++ .attached a e' :: bs₂) := by
  induction bs₁ with
  | nil => cases h with | consAttached _ hr => exact .consAttached he hr
  | cons b r ih =>
      cases b with
      | void c => cases h with | consVoid hr => exact .consVoid (ih hr)
      | attached c v => cases h with | consAttached hv hr => exact .consAttached hv (ih hr)
      | delta d => cases h with | consDelta hr => exact .consDelta (ih hr)
      | lambda f => cases h with | consLambda hr => exact .consLambda (ih hr)

/-- A parallel binding-list step never touches a key, so the two lists share a `domain`.
Proved by induction on the `ParB` derivation, no well-formedness needed. -/
theorem parB_domain {bs bs' : List Binding} (h : ParB bs bs') : domain bs = domain bs' := by
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
  | nil => rfl
  | consVoid _ ih => simp only [domain, Binding.key?]; rw [ih]
  | consAttached _ _ _ ih => simp only [domain, Binding.key?]; rw [ih]
  | consDelta _ ih => simp only [domain, Binding.key?]; rw [ih]
  | consLambda _ ih => simp only [domain, Binding.key?]; rw [ih]

/-- Bridge: a `ParB` step out of a well-formed binding list lands in a well-formed
formation — the domain is transported by `parB_domain`, while the well-formed values
`WFB bs'` are supplied by the caller (`WF.par`'s `motive₂` leg). -/
theorem wf_form_of_parB {bs bs' : List Binding}
    (hnd : (domain bs).Nodup) (hlk : ∀ a ∈ domain bs, a.legalKey = true)
    (hd : domain bs = domain bs') (hb : WFB bs') : WF (.form bs') := by
  refine .form (hd ▸ hnd) ?_ hb
  intro a ha; exact hlk a (hd ▸ ha)

/-- The value `lookup` finds in a well-formed binding list is well-formed. -/
theorem wfb_lookup_attached : ∀ {bs : List Binding} {a : Attr} {e : Term},
    WFB bs → lookup bs a = .attached e → WF e
  | [], _, _, _, h => by simp [lookup] at h
  | .void c :: r, a, e, hwfb, h => by
      simp only [lookup] at h
      cases hwfb with
      | consVoid hr =>
          split at h
          · nomatch h
          · exact wfb_lookup_attached hr h
  | .attached c v :: r, a, e, hwfb, h => by
      simp only [lookup] at h
      cases hwfb with
      | consAttached hv hr =>
          split at h
          · next _ => injection h with he; subst he; exact hv
          · exact wfb_lookup_attached hr h
  | .delta d :: r, a, e, hwfb, h => by
      simp only [lookup] at h
      cases hwfb with | consDelta hr => exact wfb_lookup_attached hr h
  | .lambda f :: r, a, e, hwfb, h => by
      simp only [lookup] at h
      cases hwfb with | consLambda hr => exact wfb_lookup_attached hr h

/-- Contextualization preserves well-formedness (it only substitutes the well-formed `b` at
`ξ`-leaves and stops at formations). Needed for `dot`, whose result embeds `C(e₁ ⊳ ⟦…⟧)`. -/
theorem wf_contextualize {b : Term} (hb : WF b) : ∀ {e : Term}, WF e → WF (contextualize e b)
  | .bot, _ => WF.bot
  | .glob, _ => WF.glob
  | .xi, _ => hb
  | .form _, he => he
  | .dispatch s a, he => by
      cases he with | dispatch hs => exact .dispatch (wf_contextualize hb hs)
  | .app s a arg, he => by
      cases he with | app hs ha => exact .app (wf_contextualize hb hs) (wf_contextualize hb ha)

/-- `fill` keeps every key (it turns a `void a` into an `attached a e`, both keyed `a`), so the
`domain` is unchanged — the engine behind `copy`'s `Nodup`/`legalKey` preservation. -/
theorem domain_fill {bs : List Binding} (a : Attr) (e : Term) : domain (fill bs a e) = domain bs := by
  induction bs with
  | nil => rfl
  | cons b r ih =>
      cases b with
      | void c =>
          by_cases hc : c = a
          · subst hc; simp [fill, domain, Binding.key?]
          · simp [fill, if_neg hc, domain, Binding.key?, ih]
      | attached c v =>
          by_cases hc : c = a
          · subst hc; simp [fill, domain, Binding.key?]
          · simp [fill, if_neg hc, domain, Binding.key?, ih]
      | delta d => simp [fill, domain, Binding.key?, ih]
      | lambda f => simp [fill, domain, Binding.key?, ih]

/-- Filling a void slot with a well-formed value preserves well-formedness of the binding list
(the new `attached a e` is well-formed by `he`; the other bindings are untouched). -/
theorem wfb_fill {a : Attr} {e : Term} (he : WF e) : ∀ {bs : List Binding}, WFB bs → WFB (fill bs a e)
  | [], _ => .nil
  | .void c :: r, hb => by
      cases hb with
      | consVoid hr =>
          by_cases hc : c = a
          · subst hc; simp only [fill, if_true]; exact .consAttached he hr
          · simp only [fill, if_neg hc]; exact .consVoid (wfb_fill he hr)
  | .attached c v :: r, hb => by
      cases hb with
      | consAttached hv hr =>
          by_cases hc : c = a
          · subst hc; simp only [fill, if_true]; exact .consAttached hv hr
          · simp only [fill, if_neg hc]; exact .consAttached hv (wfb_fill he hr)
  | .delta d :: r, hb => by
      cases hb with | consDelta hr => simp only [fill]; exact .consDelta (wfb_fill he hr)
  | .lambda f :: r, hb => by
      cases hb with | consLambda hr => simp only [fill]; exact .consLambda (wfb_fill he hr)

/-- Preservation of well-formedness under one single step (`↝`), by ordinary structural
induction on the `Step` derivation. The discard rules land in `WF.bot`; `stay` returns the
(already well-formed) subject formation; `phi` rebuilds two nested dispatches over the same
formation; `congForm` re-derives the value via `wfb_attached_wf`, the inductive hypothesis,
and `wfb_set`, transporting `Nodup`/`legalKey` across the unchanged domain by `domain_set`. -/
theorem WF.step {e e' : Term} (hwf : WF e) (h : e ↝ e') : WF e' := by
  induction h with
  | dd a => exact .bot
  | dc a e => exact .bot
  | null hv => exact .bot
  | «over» hatt hne => exact .bot
  | stop habs hphi hlam => exact .bot
  | miss habs hna => exact .bot
  | stay hs => cases hwf with | app hf _ => exact hf
  | phi hpres habs =>
      cases hwf with
      | dispatch hf => exact .dispatch (.dispatch hf)
  | alpha hget =>
      cases hwf with | app hf ha => exact .app hf ha
  | dot hl hnf =>
      cases hwf with
      | dispatch hf =>
          cases hf with
          | form hnd hlk hbb =>
              exact .app
                (wf_contextualize (.form hnd hlk hbb) (wfb_lookup_attached hbb hl))
                (.form hnd hlk hbb)
  | copy hl hxi hnf =>
      cases hwf with
      | app hf harg =>
          cases hf with
          | form hnd hlk hbb =>
              refine .form ?_ ?_ (wfb_fill harg hbb)
              · rw [domain_fill]; exact hnd
              · intro x hx; rw [domain_fill] at hx; exact hlk x hx
  | congDispatch _ ih =>
      cases hwf with | dispatch hf => exact .dispatch (ih hf)
  | congAppFn _ ih =>
      cases hwf with | app hf ha => exact .app (ih hf) ha
  | congAppArg _ ih =>
      cases hwf with | app hf ha => exact .app hf (ih ha)
  | @congForm bs₁ bs₂ a e e' hstep ih =>
      cases hwf with
      | form hnd hlk hb =>
          exact .form (domain_set ▸ hnd) (fun x hx => hlk x (domain_set ▸ hx))
            (wfb_set hb (ih (wfb_attached_wf hb)))

/-- Preservation of well-formedness under one parallel step (`Par`), proved via the
two-motive `Par.rec` recursor whose binding-list leg (`motive₂`) is exactly the
`WFB xs → WFB ys` implication. Discard rules land in `WF.bot`; `stay`/`phi`/`congForm`
rebuild the target formation through the `parB_domain`+`motive₂` bridge `wf_form_of_parB`;
the congruences thread the inductive hypotheses through the subterms. -/
theorem WF.par {e e' : Term} (hwf : WF e) (h : Par e e') : WF e' := by
  revert hwf
  induction h using Par.rec
    (motive_2 := fun xs ys _ => WFB xs → WFB ys) with
  | refl e => exact fun hw => hw
  | dd a => exact fun _ => .bot
  | dc he ihe => exact fun _ => .bot
  | null hb hl ihb => exact fun _ => .bot
  | «over» hb hl hne he ihb ihe => exact fun _ => .bot
  | stop hb h1 h2 h3 ihb => exact fun _ => .bot
  | miss hb hl hna he ihb ihe => exact fun _ => .bot
  | stay hb hl he ihb ihe =>
      intro hw
      cases hw with
      | app hf _ =>
          cases hf with
          | form hnd hlk hbb => exact wf_form_of_parB hnd hlk (parB_domain hb) (ihb hbb)
  | phi hb hpres habs ihb =>
      intro hw
      cases hw with
      | dispatch hf =>
          cases hf with
          | form hnd hlk hbb =>
              exact .dispatch (.dispatch (wf_form_of_parB hnd hlk (parB_domain hb) (ihb hbb)))
  | alpha hb hget he ihb ihe =>
      intro hw
      cases hw with
      | app hf harg =>
          cases hf with
          | form hnd hlk hbb =>
              exact .app (wf_form_of_parB hnd hlk (parB_domain hb) (ihb hbb)) (ihe harg)
  | dot hb hl0 hl1 hnf ihb =>
      intro hw
      cases hw with
      | dispatch hf =>
          cases hf with
          | form hnd hlk hbb =>
              cases wf_form_of_parB hnd hlk (parB_domain hb) (ihb hbb) with
              | form hnd' hlk' hbb' =>
                  exact .app
                    (wf_contextualize (.form hnd' hlk' hbb') (wfb_lookup_attached hbb' hl1))
                    (.form hnd' hlk' hbb')
  | copy hb hl harg hxi hnf ihb iharg =>
      intro hw
      cases hw with
      | app hf harg2 =>
          cases hf with
          | form hnd hlk hbb =>
              refine .form ?_ ?_ (wfb_fill (iharg harg2) (ihb hbb))
              · rw [domain_fill, ← parB_domain hb]; exact hnd
              · intro x hx; rw [domain_fill, ← parB_domain hb] at hx; exact hlk x hx
  | congDispatch he ihe =>
      intro hw
      cases hw with | dispatch hf => exact .dispatch (ihe hf)
  | congApp he harg ihe iharg =>
      intro hw
      cases hw with | app hf ha => exact .app (ihe hf) (iharg ha)
  | congForm hb ihb =>
      intro hw
      cases hw with
      | form hnd hlk hbb => exact wf_form_of_parB hnd hlk (parB_domain hb) (ihb hbb)
  | nil hw => exact hw
  | consVoid hb ihb hw =>
      cases hw with | consVoid hr => exact .consVoid (ihb hr)
  | consAttached hv hb ihv ihb hw =>
      cases hw with | consAttached hvw hr => exact .consAttached (ihv hvw) (ihb hr)
  | consDelta hb ihb hw =>
      cases hw with | consDelta hr => exact .consDelta (ihb hr)
  | consLambda hb ihb hw =>
      cases hw with | consLambda hr => exact .consLambda (ihb hr)

end PhiConfluence
