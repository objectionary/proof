-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Preservation

/-!
# Canonical formations — the implicit parent (`ρ`) slot

The paper (`foundations.tex`, Def. Parent) and `phino` treat **every formation as carrying a
parent attribute `ρ`, void until set** (a `this`-pointer, void until a method is called). The paper
*grammar* (`syntax.tex`) does **not** mandate `ρ` — a formation may be written `⟦⟧` — so the parent
is supplied **semantically**: `phino` materialises a `ρ↦∅` appended at the end of every formation
that lacks one (verified: `⟦x↦Φ⟧` normalises to `⟦x↦Φ, ρ↦∅⟧`, recursively, and explicit `ρ` is kept
in place). This module models that canonicalisation, closing the implicit-`ρ` fidelity gap.

* `canon` / `canonB` — the canonicalisation: recursively append `ρ↦∅` to every `ρ`-less formation
  (explicit `ρ` kept in place, never duplicated), exactly matching `phino`.
* `Canonical` / `CanonicalB` — the invariant: every formation has a `ρ` binding.
* `canon_canonical` — `canon` always produces a `Canonical` term.
* `wf_canon` — `canon` preserves well-formedness (it adds `ρ` only when absent, so no duplicate key,
  and `ρ` is a legal key).
* `step_canonical` — reduction **preserves** `Canonical`: `phino`'s term space (parent everywhere) is
  closed under our `Step`. With `canon` establishing it and reduction preserving it, the `WF`-scoped
  `confluence` (which already covers these `WF` terms) governs exactly `phino`'s canonical calculus —
  the headline no longer needs the "`ρ`-injection-free fragment" qualifier.
-/

namespace PhiConfluence

/-- Ensure a binding list carries a parent: append `ρ↦∅` at the end iff no `ρ` key is present
(matching `phino`; explicit `ρ` is kept in place, never duplicated). -/
def ensureRho (bs : List Binding) : List Binding :=
  match lookup bs .rho with
  | .absent => bs ++ [.void .rho]
  | _       => bs

mutual
/-- Canonicalise a term: make every formation carry a parent `ρ` (recursively). -/
def canon : Term → Term
  | .bot => .bot
  | .glob => .glob
  | .xi => .xi
  | .form bs => .form (ensureRho (canonB bs))
  | .dispatch e a => .dispatch (canon e) a
  | .app e a arg => .app (canon e) a (canon arg)
/-- Canonicalise every value in a binding list. -/
def canonB : List Binding → List Binding
  | [] => []
  | .void a :: r => .void a :: canonB r
  | .attached a v :: r => .attached a (canon v) :: canonB r
  | .delta d :: r => .delta d :: canonB r
  | .lambda f :: r => .lambda f :: canonB r
end

mutual
/-- A term is **canonical** when every formation in it carries a `ρ` binding — `phino`'s
parent-everywhere invariant. -/
inductive Canonical : Term → Prop where
  | bot : Canonical .bot
  | glob : Canonical .glob
  | xi : Canonical .xi
  | form {bs : List Binding} : lookup bs .rho ≠ .absent → CanonicalB bs → Canonical (.form bs)
  | dispatch {e : Term} {a : Attr} : Canonical e → Canonical (.dispatch e a)
  | app {e arg : Term} {a : Attr} : Canonical e → Canonical arg → Canonical (.app e a arg)
/-- Every value in the binding list is canonical. -/
inductive CanonicalB : List Binding → Prop where
  | nil : CanonicalB []
  | consVoid {a : Attr} {r : List Binding} : CanonicalB r → CanonicalB (.void a :: r)
  | consAttached {a : Attr} {v : Term} {r : List Binding} : Canonical v → CanonicalB r → CanonicalB (.attached a v :: r)
  | consDelta {d : List UInt8} {r : List Binding} : CanonicalB r → CanonicalB (.delta d :: r)
  | consLambda {f : String} {r : List Binding} : CanonicalB r → CanonicalB (.lambda f :: r)
end

/-- `canonB` preserves keys, hence the `domain`. -/
theorem domain_canonB (bs : List Binding) : domain (canonB bs) = domain bs := by
  induction bs with
  | nil => rfl
  | cons b r ih => cases b <;> simp [canonB, domain, Binding.key?, ih]

/-- An absent lookup means the key is not in the domain. -/
theorem lookup_absent_not_mem {a : Attr} {bs : List Binding} (h : lookup bs a = .absent) :
    a ∉ domain bs := by
  induction bs with
  | nil => simp [domain]
  | cons b r ih =>
      cases b with
      | void c =>
          simp only [lookup] at h
          split at h
          · exact absurd h (by simp)
          · rename_i hc
            simp only [domain, Binding.key?, List.mem_cons, not_or]
            exact ⟨fun he => hc he.symm, ih h⟩
      | attached c v =>
          simp only [lookup] at h
          split at h
          · exact absurd h (by simp)
          · rename_i hc
            simp only [domain, Binding.key?, List.mem_cons, not_or]
            exact ⟨fun he => hc he.symm, ih h⟩
      | delta d => simp only [lookup] at h; simp only [domain, Binding.key?]; exact ih h
      | lambda f => simp only [lookup] at h; simp only [domain, Binding.key?]; exact ih h

/-- Looking up `ρ` in a list that lacks it, after appending `ρ↦∅`, finds the appended slot. -/
theorem lookup_append_void_rho {bs : List Binding} (h : lookup bs .rho = .absent) :
    lookup (bs ++ [.void .rho]) .rho = .void := by
  induction bs with
  | nil => simp [lookup]
  | cons b r ih =>
      cases b with
      | void c =>
          simp only [lookup] at h
          split at h
          · exact absurd h (by simp)
          · rename_i hc
            simp only [List.cons_append, lookup, if_neg hc]
            exact ih h
      | attached c v =>
          simp only [lookup] at h
          split at h
          · exact absurd h (by simp)
          · rename_i hc
            simp only [List.cons_append, lookup, if_neg hc]
            exact ih h
      | delta d => simp only [lookup] at h; simp only [List.cons_append, lookup]; exact ih h
      | lambda f => simp only [lookup] at h; simp only [List.cons_append, lookup]; exact ih h

/-- `ensureRho` always yields a list with a `ρ` key. -/
theorem ensureRho_has_rho (bs : List Binding) : lookup (ensureRho bs) .rho ≠ .absent := by
  cases hl : lookup bs .rho with
  | absent => simp only [ensureRho, hl]; rw [lookup_append_void_rho hl]; simp
  | void => simp [ensureRho, hl]
  | attached v => simp [ensureRho, hl]

/-- Appending a void binding preserves `WFB`. -/
theorem wfb_append_void {a : Attr} : ∀ {bs : List Binding}, WFB bs → WFB (bs ++ [.void a])
  | [], _ => .consVoid .nil
  | _ :: _, h => by
      cases h with
      | consVoid hr => exact .consVoid (wfb_append_void hr)
      | consAttached hv hr => exact .consAttached hv (wfb_append_void hr)
      | consDelta hr => exact .consDelta (wfb_append_void hr)
      | consLambda hr => exact .consLambda (wfb_append_void hr)

/-- Appending a void binding preserves `CanonicalB`. -/
theorem canonicalB_append_void {a : Attr} : ∀ {bs : List Binding}, CanonicalB bs → CanonicalB (bs ++ [.void a])
  | [], _ => .consVoid .nil
  | _ :: _, h => by
      cases h with
      | consVoid hr => exact .consVoid (canonicalB_append_void hr)
      | consAttached hv hr => exact .consAttached hv (canonicalB_append_void hr)
      | consDelta hr => exact .consDelta (canonicalB_append_void hr)
      | consLambda hr => exact .consLambda (canonicalB_append_void hr)

/-- `WF (.form (ensureRho cs))` from the `WF` ingredients of `cs`: appending `ρ↦∅` (only when `ρ`
is absent) keeps the domain duplicate-free (`ρ` was not present) and `ρ` is a legal key. -/
theorem wf_form_ensureRho {cs : List Binding}
    (hnd : (domain cs).Nodup) (hlk : ∀ a ∈ domain cs, a.legalKey = true) (hbb : WFB cs) :
    WF (.form (ensureRho cs)) := by
  cases hl : lookup cs .rho with
  | absent =>
      simp only [ensureRho, hl]
      have hrho : domain [Binding.void Attr.rho] = [Attr.rho] := rfl
      refine .form ?_ ?_ (wfb_append_void hbb)
      · rw [domain_append, hrho]
        refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
        intro x hx b hb
        rw [List.mem_singleton] at hb
        subst hb
        intro he
        exact lookup_absent_not_mem hl (he ▸ hx)
      · intro x hx
        rw [domain_append, hrho, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact hlk x hx
        · subst hx; rfl
  | void => simp only [ensureRho, hl]; exact .form hnd hlk hbb
  | attached v => simp only [ensureRho, hl]; exact .form hnd hlk hbb

/-- `ensureRho` preserves `CanonicalB`. -/
theorem canonicalB_ensureRho {bs : List Binding} (h : CanonicalB bs) : CanonicalB (ensureRho bs) := by
  cases hl : lookup bs .rho with
  | absent => simp only [ensureRho, hl]; exact canonicalB_append_void h
  | void => simp only [ensureRho, hl]; exact h
  | attached v => simp only [ensureRho, hl]; exact h

mutual
/-- `canon` always produces a `Canonical` term. -/
theorem canon_canonical : ∀ e : Term, Canonical (canon e)
  | .bot => .bot
  | .glob => .glob
  | .xi => .xi
  | .form bs => by
      simp only [canon]
      exact .form (ensureRho_has_rho _) (canonicalB_ensureRho (canonB_canonical bs))
  | .dispatch e _ => .dispatch (canon_canonical e)
  | .app e _ arg => .app (canon_canonical e) (canon_canonical arg)
/-- `canonB` always produces a `CanonicalB` list. -/
theorem canonB_canonical : ∀ bs : List Binding, CanonicalB (canonB bs)
  | [] => .nil
  | .void _ :: r => .consVoid (canonB_canonical r)
  | .attached _ v :: r => .consAttached (canon_canonical v) (canonB_canonical r)
  | .delta _ :: r => .consDelta (canonB_canonical r)
  | .lambda _ :: r => .consLambda (canonB_canonical r)
end

mutual
/-- `canon` preserves well-formedness. -/
theorem wf_canon : ∀ {e : Term}, WF e → WF (canon e)
  | .bot, _ => .bot
  | .glob, _ => .glob
  | .xi, _ => .xi
  | .form bs, h => by
      cases h with
      | form hnd hlk hbb =>
        simp only [canon]
        exact wf_form_ensureRho (by rw [domain_canonB]; exact hnd)
          (by rw [domain_canonB]; exact hlk) (wfb_canonB hbb)
  | .dispatch e _, h => by cases h with | dispatch he => exact .dispatch (wf_canon he)
  | .app e _ arg, h => by cases h with | app he ha => exact .app (wf_canon he) (wf_canon ha)
/-- `canonB` preserves `WFB`. -/
theorem wfb_canonB : ∀ {bs : List Binding}, WFB bs → WFB (canonB bs)
  | [], _ => .nil
  | .void _ :: _, h => by cases h with | consVoid hr => exact .consVoid (wfb_canonB hr)
  | .attached _ v :: _, h => by cases h with | consAttached hv hr => exact .consAttached (wf_canon hv) (wfb_canonB hr)
  | .delta _ :: _, h => by cases h with | consDelta hr => exact .consDelta (wfb_canonB hr)
  | .lambda _ :: _, h => by cases h with | consLambda hr => exact .consLambda (wfb_canonB hr)
end

/-! ### Reduction preserves `Canonical` (`phino`'s term space is closed under `Step`) -/

/-- An absent lookup follows from non-membership in the domain (converse of `lookup_absent_not_mem`). -/
theorem not_mem_domain_lookup_absent {a : Attr} {bs : List Binding} (h : a ∉ domain bs) :
    lookup bs a = .absent := by
  induction bs with
  | nil => rfl
  | cons b r ih =>
      cases b with
      | void c =>
          simp only [domain, Binding.key?, List.mem_cons, not_or] at h
          simp only [lookup, if_neg (Ne.symm h.1)]; exact ih h.2
      | attached c v =>
          simp only [domain, Binding.key?, List.mem_cons, not_or] at h
          simp only [lookup, if_neg (Ne.symm h.1)]; exact ih h.2
      | delta d => simp only [domain, Binding.key?] at h; simp only [lookup]; exact ih h
      | lambda f => simp only [domain, Binding.key?] at h; simp only [lookup]; exact ih h

/-- A present (non-absent) lookup key is in the domain. -/
theorem lookup_ne_absent_mem {a : Attr} {bs : List Binding} (h : lookup bs a ≠ .absent) :
    a ∈ domain bs := by
  by_contra hc; exact h (not_mem_domain_lookup_absent hc)

/-- A key in the domain has a non-absent lookup. -/
theorem mem_domain_lookup_ne_absent {a : Attr} {bs : List Binding} (h : a ∈ domain bs) :
    lookup bs a ≠ .absent := fun habs => lookup_absent_not_mem habs h

/-- The value at one position of a `CanonicalB` list is canonical. -/
theorem canonicalB_attached_canon {bs₁ bs₂ : List Binding} {a : Attr} {e : Term}
    (h : CanonicalB (bs₁ ++ .attached a e :: bs₂)) : Canonical e := by
  induction bs₁ with
  | nil => cases h with | consAttached hv _ => exact hv
  | cons b r ih =>
      cases b with
      | void c => cases h with | consVoid hr => exact ih hr
      | attached c v => cases h with | consAttached _ hr => exact ih hr
      | delta d => cases h with | consDelta hr => exact ih hr
      | lambda f => cases h with | consLambda hr => exact ih hr

/-- Replacing one attached value by another canonical term preserves `CanonicalB`. -/
theorem canonicalB_set {bs₁ bs₂ : List Binding} {a : Attr} {e e' : Term}
    (h : CanonicalB (bs₁ ++ .attached a e :: bs₂)) (he : Canonical e') :
    CanonicalB (bs₁ ++ .attached a e' :: bs₂) := by
  induction bs₁ with
  | nil => cases h with | consAttached _ hr => exact .consAttached he hr
  | cons b r ih =>
      cases b with
      | void c => cases h with | consVoid hr => exact .consVoid (ih hr)
      | attached c v => cases h with | consAttached hv hr => exact .consAttached hv (ih hr)
      | delta d => cases h with | consDelta hr => exact .consDelta (ih hr)
      | lambda f => cases h with | consLambda hr => exact .consLambda (ih hr)

/-- The value `lookup` finds in a `CanonicalB` list is canonical. -/
theorem canonicalB_lookup_attached : ∀ {bs : List Binding} {a : Attr} {e : Term},
    CanonicalB bs → lookup bs a = .attached e → Canonical e
  | [], _, _, _, h => by simp [lookup] at h
  | .void c :: r, a, e, hcb, h => by
      simp only [lookup] at h
      cases hcb with
      | consVoid hr => split at h
                       · nomatch h
                       · exact canonicalB_lookup_attached hr h
  | .attached c v :: r, a, e, hcb, h => by
      simp only [lookup] at h
      cases hcb with
      | consAttached hv hr => split at h
                              · next _ => injection h with he; subst he; exact hv
                              · exact canonicalB_lookup_attached hr h
  | .delta d :: r, a, e, hcb, h => by
      simp only [lookup] at h
      cases hcb with | consDelta hr => exact canonicalB_lookup_attached hr h
  | .lambda f :: r, a, e, hcb, h => by
      simp only [lookup] at h
      cases hcb with | consLambda hr => exact canonicalB_lookup_attached hr h

/-- Contextualisation preserves `Canonical` (it only substitutes the canonical `b` at `ξ`-leaves
and stops at formations) — needed for `dot`, whose result embeds `C(e₁ ⊳ ⟦…⟧)`. -/
theorem canonical_contextualize {b : Term} (hb : Canonical b) :
    ∀ {e : Term}, Canonical e → Canonical (contextualize e b)
  | .bot, _ => .bot
  | .glob, _ => .glob
  | .xi, _ => hb
  | .form _, he => he
  | .dispatch s a, he => by cases he with | dispatch hs => exact .dispatch (canonical_contextualize hb hs)
  | .app s a arg, he => by cases he with | app hs ha => exact .app (canonical_contextualize hb hs) (canonical_contextualize hb ha)

/-- Filling a void slot with a canonical value preserves `CanonicalB`. -/
theorem canonical_fill {a : Attr} {e : Term} (he : Canonical e) :
    ∀ {bs : List Binding}, CanonicalB bs → CanonicalB (fill bs a e)
  | [], _ => .nil
  | .void c :: r, hb => by
      cases hb with
      | consVoid hr =>
          by_cases hc : c = a
          · subst hc; simp only [fill, if_true]; exact .consAttached he hr
          · simp only [fill, if_neg hc]; exact .consVoid (canonical_fill he hr)
  | .attached c v :: r, hb => by
      cases hb with
      | consAttached hv hr =>
          by_cases hc : c = a
          · subst hc; simp only [fill, if_true]; exact .consAttached hv hr
          · simp only [fill, if_neg hc]; exact .consAttached hv (canonical_fill he hr)
  | .delta d :: r, hb => by cases hb with | consDelta hr => simp only [fill]; exact .consDelta (canonical_fill he hr)
  | .lambda f :: r, hb => by cases hb with | consLambda hr => simp only [fill]; exact .consLambda (canonical_fill he hr)

/-- **Reduction preserves `Canonical`.** One `Step` out of a canonical term lands in a canonical
term — `phino`'s parent-everywhere term space is closed under our `Step`. Discard rules land in
`Canonical.bot`; `stay` returns the (canonical) subject; `dot`/`copy` keep the formation's `ρ` (its
`domain` is unchanged by `contextualize`/`fill`, transported via `domain_fill`/`domain_set` +
`mem_domain_lookup_ne_absent`) and rebuild the value canonically; `alpha` only renames a key. Mirrors
`WF.step`. -/
theorem step_canonical {e e' : Term} (hc : Canonical e) (h : e ↝ e') : Canonical e' := by
  induction h with
  | dd a => exact .bot
  | dc a e => exact .bot
  | null hv => exact .bot
  | «over» hatt hne => exact .bot
  | stop habs hphi hlam => exact .bot
  | miss habs hna => exact .bot
  | stay hs => cases hc with | app hf _ => exact hf
  | phi hpres habs => cases hc with | dispatch hf => exact .dispatch (.dispatch hf)
  | alpha hget => cases hc with | app hf ha => exact .app hf ha
  | dot hl hnf =>
      cases hc with
      | dispatch hf =>
          cases hf with
          | form hrho hbb =>
              exact .app
                (canonical_contextualize (.form hrho hbb) (canonicalB_lookup_attached hbb hl))
                (.form hrho hbb)
  | copy hl hxi hnf =>
      cases hc with
      | app hf harg =>
          cases hf with
          | form hrho hbb =>
              refine .form ?_ (canonical_fill harg hbb)
              exact mem_domain_lookup_ne_absent (by rw [domain_fill]; exact lookup_ne_absent_mem hrho)
  | congDispatch _ ih => cases hc with | dispatch hf => exact .dispatch (ih hf)
  | congAppFn _ ih => cases hc with | app hf ha => exact .app (ih hf) ha
  | congAppArg _ ih => cases hc with | app hf ha => exact .app hf (ih ha)
  | @congForm bs₁ bs₂ a e e' hstep ih =>
      cases hc with
      | form hrho hb =>
          refine .form ?_ (canonicalB_set hb (ih (canonicalB_attached_canon hb)))
          exact mem_domain_lookup_ne_absent (domain_set ▸ lookup_ne_absent_mem hrho)

end PhiConfluence
