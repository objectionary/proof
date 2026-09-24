-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Step

/-!
# Executable reducer

The relation `Step` is declarative (it allows *any* legal reduction). To actually run programs and
print traces, we add an executable, deterministic `reduceStep`. It first tries every rule at the
root (`rootStep`: `dd, dc, null, over, stop, miss, stay, alpha, overa, amiss, dot, copy, dl`); when
none fires or its guard is blocked (e.g. `dot` needs `nf e₁`), it recurses **into the subterms** —
the subject first, then the argument, and a formation's bindings in list order (`reduceForm`, the
executable counterpart of `congForm`) — so a redex buried inside a formation is found, not missed.
`trace` iterates it (bounded by fuel, since the full calculus is non-terminating — `dot`'s
`ρ`-feedback can diverge).

`reduceStep` is the runnable counterpart of `Step`, certified by
`reduce_sound : reduceStep e = some e' → e ↝ e'`: every step it takes — hence every step the demo
prints — is a genuine `Step`, governed by the confluence theorem. It is **soundness**
(`reduceStep ⊆ Step`), one deterministic choice per call: `rootStep_sound` covers the root, and a
`Term` induction covers the congruences.
-/

namespace PhiConfluence

/-- The root contraction of an application `⟦bs⟧(a ↦ arg)` by a non-positional `a`: `stay`,
`over`, `miss`, or `copy` when the argument is `ξ`-free and normal. -/
def rootAttr (bs : List Binding) (a : Attr) (arg : Term) : Option Term :=
  match lookup bs a with
  | .attached _ => if a = .rho then some (.form bs) else some .bot
  | .absent => some .bot
  | .void => if xiFree arg && nf arg then some (.form (fill bs a arg)) else none

/-- The contraction of a redex at the root of the term, or `none` if no rule fires there. -/
def rootStep : Term → Option Term
  | .form bs => if hasLambda bs && hasDelta bs then some .bot else none
  | .dispatch .bot _ => some .bot
  | .dispatch (.form bs) a =>
      match lookup bs a with
      | .void => some .bot
      | .attached e₁ =>
          if nf e₁ && !(hasLambda bs && hasDelta bs) then
            some (.app (contextualize e₁ (.form (ensureRho (erase bs a)))) .rho (.form bs))
          else none
      | .absent =>
          match lookup bs .phi with
          | .absent => if hasLambda bs then none else some .bot
          | _ => none
  | .app .bot _ _ => some .bot
  | .app (.form bs) (.alpha i) arg =>
      match ordinal bs i with
      | none => some .bot
      | some τ =>
          match lookup bs τ with
          | .void => some (.app (.form bs) τ arg)
          | .attached _ => some .bot
          | .absent => none
  | .app (.form bs) a arg => rootAttr bs a arg
  | _ => none

mutual
/-- One deterministic reduction step, or `none` if normal: a root redex first, then the subject,
the argument, and the formation bindings. -/
def reduceStep (e : Term) : Option Term :=
  match rootStep e with
  | some e' => some e'
  | none =>
    match e with
    | .dispatch s a => (reduceStep s).map (fun s' => Term.dispatch s' a)
    | .app s a arg =>
      match reduceStep s with
      | some s' => some (Term.app s' a arg)
      | none => (reduceStep arg).map (fun arg' => Term.app s a arg')
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
  | .void a :: r => (reduceForm r).map (fun r' => .void a :: r')
  | .delta d :: r => (reduceForm r).map (fun r' => .delta d :: r')
  | .lambda f :: r => (reduceForm r).map (fun r' => .lambda f :: r')
end

/-- The reduction sequence from `e`, up to `fuel` steps. -/
def trace : Nat → Term → List Term
  | 0, e => [e]
  | fuel + 1, e =>
    match reduceStep e with
    | none => [e]
    | some e' => e :: trace fuel e'

/-- Prepend a binding to a formation-step (the executable counterpart of `congForm`'s cons-lift,
needed for `reduceForm`'s tail recursion); `dl` cannot land on a formation. -/
theorem formStepCons {bs bs' : List Binding} (b : Binding) (h : Step (.form bs) (.form bs')) :
    Step (.form (b :: bs)) (.form (b :: bs')) := by
  cases h with | congForm st => exact Step.congForm (bs₁ := b :: _) st

/-- `rootAttr` contracts only genuine `Step` redexes. -/
theorem rootAttr_sound {bs : List Binding} {a : Attr} {arg e' : Term} (hna : a.isAlpha = false)
    (h : rootAttr bs a arg = some e') : Step (.app (.form bs) a arg) e' := by
  cases hl : lookup bs a with
  | attached v =>
      by_cases hr : a = .rho
      · subst hr
        simp only [rootAttr, hl, if_true, Option.some.injEq] at h
        subst h; exact Step.stay hl
      · simp only [rootAttr, hl, hr, if_false, Option.some.injEq] at h
        subst h; exact Step.over hl hr
  | absent =>
      simp only [rootAttr, hl, Option.some.injEq] at h
      subst h; exact Step.miss hl hna
  | void =>
      by_cases hg : (xiFree arg && nf arg) = true
      · simp only [rootAttr, hl, hg, if_true, Option.some.injEq] at h
        subst h
        obtain ⟨hxi, hnf⟩ := Bool.and_eq_true_iff.mp hg
        exact Step.copy hl hxi hnf
      · simp [rootAttr, hl, hg] at h

/-- `rootStep` contracts only genuine `Step` redexes. -/
theorem rootStep_sound : ∀ {e e' : Term}, rootStep e = some e' → e ↝ e'
  | .form bs, e', h => by
      by_cases hld : (hasLambda bs && hasDelta bs) = true
      · simp only [rootStep, hld, if_true, Option.some.injEq] at h
        subst h
        obtain ⟨hl, hd⟩ := Bool.and_eq_true_iff.mp hld
        exact Step.dl hl hd
      · simp [rootStep, hld] at h
  | .dispatch .bot a, e', h => by
      simp only [rootStep, Option.some.injEq] at h; subst h; exact Step.dd a
  | .dispatch (.form bs) a, e', h => by
      cases hl : lookup bs a with
      | void => simp only [rootStep, hl, Option.some.injEq] at h; subst h; exact Step.null hl
      | attached e₁ =>
          by_cases hg : (nf e₁ && !(hasLambda bs && hasDelta bs)) = true
          · simp only [rootStep, hl, hg, if_true, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
            exact Step.dot hl hg.1 hg.2
          · simp only [rootStep, hl, hg, if_false, reduceCtorEq] at h
      | absent =>
          cases hphi : lookup bs .phi with
          | absent =>
              cases hlam : hasLambda bs with
              | true => simp [rootStep, hl, hphi, hlam] at h
              | false =>
                  simp only [rootStep, hl, hphi, hlam, Bool.false_eq_true, if_false,
                    Option.some.injEq] at h
                  subst h; exact Step.stop hl hphi hlam
          | void => simp [rootStep, hl, hphi] at h
          | attached _ => simp [rootStep, hl, hphi] at h
  | .dispatch .glob _, _, h => by simp [rootStep] at h
  | .dispatch .xi _, _, h => by simp [rootStep] at h
  | .dispatch (.dispatch _ _) _, _, h => by simp [rootStep] at h
  | .dispatch (.app _ _ _) _, _, h => by simp [rootStep] at h
  | .app .bot a arg, e', h => by
      simp only [rootStep, Option.some.injEq] at h; subst h; exact Step.dc a arg
  | .app (.form bs) (.alpha i) arg, e', h => by
      cases hord : ordinal bs i with
      | none => simp only [rootStep, hord, Option.some.injEq] at h; subst h; exact Step.amiss hord
      | some τ =>
          cases hl : lookup bs τ with
          | void =>
              simp only [rootStep, hord, hl, Option.some.injEq] at h; subst h; exact Step.alpha hord hl
          | attached v =>
              simp only [rootStep, hord, hl, Option.some.injEq] at h; subst h; exact Step.overa hord hl
          | absent => simp [rootStep, hord, hl] at h
  | .app (.form bs) .phi arg, _, h => rootAttr_sound rfl h
  | .app (.form bs) .rho arg, _, h => rootAttr_sound rfl h
  | .app (.form bs) (.label _) arg, _, h => rootAttr_sound rfl h
  | .app .glob _ _, _, h => by simp [rootStep] at h
  | .app .xi _ _, _, h => by simp [rootStep] at h
  | .app (.dispatch _ _) _ _, _, h => by simp [rootStep] at h
  | .app (.app _ _ _) _ _, _, h => by simp [rootStep] at h
  | .bot, _, h => by simp [rootStep] at h
  | .glob, _, h => by simp [rootStep] at h
  | .xi, _, h => by simp [rootStep] at h

/-- A reducer step is a root contraction, or else whatever the congruence branch derives. -/
theorem sound_of_root {e e' : Term} (hc : rootStep e = none → reduceStep e = some e' → e ↝ e')
    (h : reduceStep e = some e') : e ↝ e' := by
  cases hr : rootStep e with
  | none => exact hc hr h
  | some r =>
      rw [reduceStep.eq_def, hr] at h
      injection h with h
      subst h
      exact rootStep_sound hr

/-- Soundness of the executable reducer: every step it takes is a genuine `Step`. By the `Term`
recursor: the root is `rootStep_sound`, the subterm recursion follows the congruence rules, and
the binding-list leg (`motive₃`) is discharged with `formStepCons` and `Step.congForm`. -/
theorem reduce_sound {e e' : Term} (h : reduceStep e = some e') : e ↝ e' := by
  revert e'
  induction e using Term.rec
    (motive_2 := fun b => ∀ a v, b = Binding.attached a v →
      ∀ v', reduceStep v = some v' → v ↝ v')
    (motive_3 := fun bs => ∀ bs', reduceForm bs = some bs' → Step (.form bs) (.form bs')) with
  | bot => intro e' h; exact sound_of_root (fun hr h => by rw [reduceStep.eq_def, hr] at h; simp at h) h
  | glob => intro e' h; exact sound_of_root (fun hr h => by rw [reduceStep.eq_def, hr] at h; simp at h) h
  | xi => intro e' h; exact sound_of_root (fun hr h => by rw [reduceStep.eq_def, hr] at h; simp at h) h
  | form bs ih =>
      intro e' h
      refine sound_of_root (fun hr h => ?_) h
      rw [reduceStep.eq_def, hr] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      exact ih _ hbs'
  | dispatch s a ihs =>
      intro e' h
      refine sound_of_root (fun hr h => ?_) h
      rw [reduceStep.eq_def, hr] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨s', hs', rfl⟩ := h
      exact Step.congDispatch (ihs hs')
  | app s a arg ihs iharg =>
      intro e' h
      refine sound_of_root (fun hr h => ?_) h
      rw [reduceStep.eq_def, hr] at h
      cases hs : reduceStep s with
      | some s' =>
          simp only [hs, Option.some.injEq] at h
          subst h; exact Step.congAppFn (ihs hs)
      | none =>
          simp only [hs, Option.map_eq_some_iff] at h
          obtain ⟨arg', harg', rfl⟩ := h
          exact Step.congAppArg (iharg harg')
  | nil => rename_i bs' h; simp [reduceForm] at h
  | cons b r ihb ihr =>
      rename_i bs' h
      cases b with
      | attached a v =>
          cases hv : reduceStep v with
          | some v' =>
              simp only [reduceForm, hv, Option.some.injEq] at h
              subst h; exact Step.congForm (bs₁ := []) (ihb a v rfl _ hv)
          | none =>
              simp only [reduceForm, hv, Option.map_eq_some_iff] at h
              obtain ⟨r', hr', rfl⟩ := h
              exact formStepCons _ (ihr _ hr')
      | void a =>
          simp only [reduceForm, Option.map_eq_some_iff] at h
          obtain ⟨r', hr', rfl⟩ := h
          exact formStepCons _ (ihr _ hr')
      | delta d =>
          simp only [reduceForm, Option.map_eq_some_iff] at h
          obtain ⟨r', hr', rfl⟩ := h
          exact formStepCons _ (ihr _ hr')
      | lambda f =>
          simp only [reduceForm, Option.map_eq_some_iff] at h
          obtain ⟨r', hr', rfl⟩ := h
          exact formStepCons _ (ihr _ hr')
  | void a => rename_i hb _ _; nomatch hb
  | attached a v ihv => rename_i hb _ hv; injection hb with _ hvv; subst hvv; exact ihv hv
  | delta d => rename_i hb _ _; nomatch hb
  | lambda f => rename_i hb _ _; nomatch hb

end PhiConfluence
