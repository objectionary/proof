-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Step

/-!
# Executable reducer

The relation `Step` is declarative (it allows *any* legal reduction). To actually run programs and
print traces, we add an executable, deterministic `reduceStep`: it finds the leftmost-outermost
redex among **all eleven rules** (`dd, dc, null, over, stop, miss, stay, phi, alpha, dot, copy`)
and returns the reduct, or `none`. When a root rule is *guard-blocked* (e.g. `dot` needs `nf e₁`) or
absent, it recurses **into the subterms — including a formation's bindings** (`reduceForm`, the
executable counterpart of `congForm`), so a redex buried inside a formation is found, not missed.
`trace` iterates it (bounded by fuel, since the full calculus is non-terminating — `dot`'s
`ρ`-feedback can diverge).

`reduceStep` is the runnable counterpart of `Step`, certified by
`reduce_sound : reduceStep e = some e' → e ↝ e'`: every step it takes — hence every step the demo
prints — is a genuine `Step`, governed by the confluence theorem. It is **soundness**
(`reduceStep ⊆ Step`), one deterministic choice per call. Proved by functional induction over
`reduceStep.induct`; its `motive_2` leg handles the formation-interior (`reduceForm`) recursion,
discharged with the local `formStepCons` (cons-lift of `congForm`) and `Step.congForm`. With that
branch the reducer now searches formation interiors, so `trace`/`normalForm` are reliable on
arbitrary terms (e.g. `⟦x↦(⊥.z)⟧.x` now reduces via `congForm`/`dd` instead of being wrongly
reported normal).
-/

namespace PhiConfluence

mutual
/-- One deterministic reduction step (leftmost-outermost), or `none` if normal. When no root rule
fires or its guard is blocked, recurses into subterms — including formation bindings (`reduceForm`). -/
def reduceStep : Term → Option Term
  | .dispatch s a =>
    match s with
    | .bot => some .bot
    | .form bs =>
      match lookup bs a with
      | .void => some .bot
      | .attached e₁ =>
        if nf e₁ then some (.app (contextualize e₁ (.form bs)) .rho (.form bs))
        else (reduceForm bs).map (fun bs' => Term.dispatch (Term.form bs') a)
      | .absent =>
        match lookup bs .phi with
        | .absent =>
          if hasLambda bs then (reduceForm bs).map (fun bs' => Term.dispatch (Term.form bs') a)
          else some .bot
        | _ => some (.dispatch (.dispatch (.form bs) .phi) a)
    | other => (reduceStep other).map (fun s' => Term.dispatch s' a)
  | .app s a arg =>
    match s with
    | .bot => some .bot
    | .form bs =>
      match lookup bs a with
      | .attached _ =>
        if a = Attr.rho then some (.form bs)
        else some .bot
      | .absent =>
        if a.isAlpha then
          match a with
          | .alpha i =>
            match bs[i]? with
            | some (.void τ₁) => some (.app (.form bs) τ₁ arg)
            | _ =>
              match reduceStep arg with
              | some arg' => some (Term.app (Term.form bs) a arg')
              | none => (reduceForm bs).map (fun bs' => Term.app (Term.form bs') a arg)
          | _ => some .bot
        else some .bot
      | .void =>
        if xiFree arg && nf arg then some (.form (fill bs a arg))
        else
          match reduceStep arg with
          | some arg' => some (Term.app (Term.form bs) a arg')
          | none => (reduceForm bs).map (fun bs' => Term.app (Term.form bs') a arg)
    | other =>
      match reduceStep other with
      | some s' => some (Term.app s' a arg)
      | none => (reduceStep arg).map (fun arg' => Term.app other a arg')
  | .form bs => (reduceForm bs).map Term.form
  | _ => none
/-- Reduce the first binding (in list order) whose attached value reduces; the executable
counterpart of `congForm`. `none` if every value is already normal. -/
def reduceForm : List Binding → Option (List Binding)
  | [] => none
  | .attached a e :: r =>
    match reduceStep e with
    | some e' => some (.attached a e' :: r)
    | none => (reduceForm r).map (fun r' => .attached a e :: r')
  | b :: r => (reduceForm r).map (fun r' => b :: r')
end

/-- The reduction sequence from `e`, up to `fuel` steps. -/
def trace : Nat → Term → List Term
  | 0, e => [e]
  | fuel + 1, e =>
    match reduceStep e with
    | none => [e]
    | some e' => e :: trace fuel e'

/-- Inversion: a `Step` out of a formation is a `congForm`. (Local; `LocalConfluence`/`Parallel`
have the shared versions, but both are downstream of `Reduce`.) -/
theorem formStepInv {L : List Binding} {b : Term} (h : Step (.form L) b) :
    ∃ (cs₁ : List Binding) (c : Attr) (f f' : Term) (cs₂ : List Binding),
      L = cs₁ ++ .attached c f :: cs₂ ∧ b = .form (cs₁ ++ .attached c f' :: cs₂) ∧ f ↝ f' := by
  cases h with | congForm st => exact ⟨_, _, _, _, _, rfl, rfl, st⟩

/-- Prepend a binding to a formation-step (the executable counterpart of `congForm`'s cons-lift,
needed for `reduceForm`'s tail recursion). -/
theorem formStepCons {bs bs' : List Binding} (b : Binding) (h : Step (.form bs) (.form bs')) :
    Step (.form (b :: bs)) (.form (b :: bs')) := by
  obtain ⟨cs₁, c, f, f', cs₂, hbs, hbs', hf⟩ := formStepInv h
  injection hbs' with hbs'
  subst hbs; subst hbs'
  exact Step.congForm (bs₁ := b :: cs₁) hf

/-- Soundness of the executable reducer: every step it takes is a genuine `Step`. By functional
induction over `reduceStep.induct`; the formation-interior recursion (`reduceForm`) is the
`motive_2` leg, discharged with `formStepCons` (cons-lift) and `Step.congForm`. -/
theorem reduce_sound : ∀ {e e' : Term}, reduceStep e = some e' → e ↝ e' := by
  intro e
  induction e using reduceStep.induct
    (motive_2 := fun bs => ∀ (bs' : List Binding), reduceForm bs = some bs' →
      Step (Term.form bs) (Term.form bs')) with
  | case1 a => intro e' h; simp only [reduceStep, Option.some.injEq] at h; subst h; exact Step.dd a
  | case2 a bs hv =>
      intro e' h; simp only [reduceStep, hv, Option.some.injEq] at h; subst h; exact Step.null hv
  | case3 a bs e₁ hatt hnf =>
      intro e' h
      simp only [reduceStep, hatt, hnf, if_true, Option.some.injEq] at h
      subst h; exact Step.dot hatt hnf
  | case4 a bs e₁ hatt hnf ih2 =>
      intro e' h
      simp only [reduceStep, hatt, if_neg hnf, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      exact Step.congDispatch (ih2 _ hbs')
  | case5 a bs habs hphi hlam ih2 =>
      intro e' h
      simp only [reduceStep, habs, hphi, hlam, if_true, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      exact Step.congDispatch (ih2 _ hbs')
  | case6 a bs habs hphi hlam =>
      intro e' h
      simp only [reduceStep, habs, hphi, if_neg hlam, Option.some.injEq] at h
      subst h; exact Step.stop habs hphi (by simpa using hlam)
  | case7 a bs habs hphi =>
      intro e' h
      cases hp : lookup bs .phi with
      | absent => exact absurd hp hphi
      | void => simp only [reduceStep, habs, hp] at h; injection h with h; subst h
                exact Step.phi (by simp [hp]) habs
      | attached w => simp only [reduceStep, habs, hp] at h; injection h with h; subst h
                      exact Step.phi (by simp [hp]) habs
  | case8 a other hb hf ih =>
      intro e' h
      simp only [reduceStep, Option.map_eq_some_iff] at h
      obtain ⟨s0, hs0, rfl⟩ := h
      exact Step.congDispatch (ih hs0)
  | case9 a arg => intro e' h; simp only [reduceStep, Option.some.injEq] at h; subst h; exact Step.dc a arg
  | case10 arg bs value hl =>
      intro e' h
      simp only [reduceStep, hl] at h; injection h with h; subst h; exact Step.stay hl
  | case11 a arg bs value hl hne =>
      intro e' h
      simp only [reduceStep, hl, if_neg hne, Option.some.injEq] at h
      subst h; exact Step.over hl hne
  | case12 arg bs i τ₁ hidx habs hisalpha =>
      intro e' h
      simp only [reduceStep, habs, hisalpha, if_true, hidx, Option.some.injEq] at h
      subst h; exact Step.alpha hidx
  | case13 arg bs i arg' hargsome hnotvoid habs hisalpha iharg =>
      intro e' h
      simp only [reduceStep, habs, hisalpha, if_true, hargsome, Option.some.injEq] at h
      subst h; exact Step.congAppArg (iharg hargsome)
  | case14 arg bs i hargnone hnotvoid habs hisalpha iharg ih2 =>
      intro e' h
      simp only [reduceStep, habs, hisalpha, if_true, hargnone, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      exact Step.congAppFn (ih2 _ hbs')
  | case15 a arg bs habs hisalpha hnotalpha =>
      intro e' h
      cases a with
      | phi => simp [Attr.isAlpha] at hisalpha
      | rho => simp [Attr.isAlpha] at hisalpha
      | label n => simp [Attr.isAlpha] at hisalpha
      | alpha i => exact absurd rfl (hnotalpha i)
  | case16 a arg bs habs hna =>
      intro e' h
      simp only [reduceStep, habs, if_neg hna, Option.some.injEq] at h
      subst h; exact Step.miss habs (by simpa using hna)
  | case17 a arg bs hv hguard =>
      intro e' h
      simp only [reduceStep, hv, hguard, if_true, Option.some.injEq] at h
      subst h
      obtain ⟨hxi, hnf⟩ := Bool.and_eq_true _ _ |>.mp hguard
      exact Step.copy hv hxi hnf
  | case18 a arg bs hv hgf arg' hargsome iharg =>
      intro e' h
      simp only [reduceStep, hv, if_neg hgf, hargsome, Option.some.injEq] at h
      subst h; exact Step.congAppArg (iharg hargsome)
  | case19 a arg bs hv hgf hargnone iharg ih2 =>
      intro e' h
      simp only [reduceStep, hv, if_neg hgf, hargnone, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      exact Step.congAppFn (ih2 _ hbs')
  | case20 a arg other hb hf arg' hothersome ihother =>
      intro e' h
      simp only [reduceStep, hothersome, Option.some.injEq] at h
      subst h; exact Step.congAppFn (ihother hothersome)
  | case21 a arg other hb hf hothernone ihother iharg =>
      intro e' h
      simp only [reduceStep, hothernone] at h
      cases hx : reduceStep arg with
      | none => simp [hx] at h
      | some arg0 => simp only [hx, Option.map_some, Option.some.injEq] at h
                     subst h; exact Step.congAppArg (iharg hx)
  | case22 bs ih2 =>
      intro e' h
      simp only [reduceStep, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      exact ih2 _ hbs'
  | case23 t hnd hna hnf =>
      intro e' h
      cases t with
      | bot => simp [reduceStep] at h
      | glob => simp [reduceStep] at h
      | xi => simp [reduceStep] at h
      | form bs => exact absurd rfl (hnf bs)
      | dispatch s a => exact absurd rfl (hnd s a)
      | app s a arg => exact absurd rfl (hna s a arg)
  | case24 => rename_i bs' h; simp [reduceForm] at h
  | case25 a e r arg' hesome ihe =>
      rename_i bs' h
      simp only [reduceForm, hesome, Option.some.injEq] at h
      subst h; exact Step.congForm (bs₁ := []) (ihe hesome)
  | case26 a e r henone ihe ih2r =>
      rename_i bs' h
      simp only [reduceForm, henone, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      exact formStepCons (.attached a e) (ih2r _ hr')
  | case27 b r hnotattached ih2r =>
      rename_i bs' h
      simp only [reduceForm, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      exact formStepCons b (ih2r _ hr')

end PhiConfluence
