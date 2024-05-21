set_option autoImplicit false

/-!

## References

* [Marcelo Fiore and Dmitrij Szamozvancev. 2022. Formal Metatheory of Second-Order Abstract Syntax.][FS22]
-/

variable (T : Type) -- fixed set of types

/-- Context [FS22, Section 2.1] -/
@[reducible]
def Ctx := List T

/-- Families (context-indexed sets) [FS22, Section 2.1] -/
def Family  := (Ctx T) → Type
/-- Sorted Families (sort-indexed family) [FS22, Section 2.1] -/
def Familyₛ := T → (Ctx T) → Type

/-- De-Bruijn index into the context [FS22, Section 2.1] -/
inductive I {T : Type} : Familyₛ T where
  | new
    : { α : T }
    → { ctx : Ctx T }
    → I α (α :: ctx)
  | old
    : { α β : T }
    → { ctx : Ctx T }
    → I α ctx
    → I α (β :: ctx)

/-- Maps between sorted families [FS22, Section 2.1] -/
def s_family_map
  {T: Type}
  (X : Familyₛ T)
  (Y : Familyₛ T)
  := {α : T} → {ctx : Ctx T} → X α ctx → Y α ctx

namespace Ctx
  -- def inl {X : Familyₛ} {α : T} {Γ : Ctx} (Δ : Ctx) (t : X α Γ)
  --   : X α (concat Γ Δ)
  --   := _

  -- def inr {X : Familyₛ} {α : T} (Γ : Ctx) {Δ : Ctx} (t : X α Δ)
  --   : X α (concat Γ Δ)
  --   := _

  /-- Context extension [FS22, Section 2.1] -/
  def extend (Θ : Ctx T) (X : Familyₛ T) : Familyₛ T
    := λ α Γ => X α (Θ ++ Γ)

  /-- Context map [FS22, Section 2.1.1] -/
  def map {T : Type} (Γ : Ctx T) (X : Familyₛ T) (Δ : Ctx T) : Type
    := {α : T} → I α Γ → X α Δ

  def submap {T: Type} {α : T} {Γ : Ctx T} {X : Familyₛ T} {Δ : Ctx T}
    : map (α :: Γ) X Δ → map Γ X Δ
    := λ m _ loc => m (I.old loc)

  /-- Renaming [FS22, Section 2.1.1] -/
  def rename {T : Type} (Γ : Ctx T) (Δ : Ctx T) : Type
    := map Γ I Δ

  /-- Universal copairing [FS22, Section 2.1.1] -/
  def copair {T : Type} {Γ Δ Θ : Ctx T} {X : Familyₛ T}
    : (map Γ X Θ) → (map Δ X Θ) → (map (Γ ++ Δ) X Θ)
    := λ map1 map2 {α} loc => match Γ with
      | [] => map2 loc
      | β :: ctx => by
        simp [List.append] at loc
        match loc with
        | I.new => exact map1 I.new
        | I.old tail => exact (copair (submap map1) map2) tail

  /-- Adding a single term to substitution [FS22, Section 2.1.1] -/
  def add {T: Type} (X : Familyₛ T) {α : T} {Γ Δ : Ctx T} (t : X α Δ)
    : map Γ X Δ → map (α :: Γ) X Δ
    := λ m =>
      let singleton : map ([α]) X Δ := λ loc => match loc with
        | I.new => t
      copair singleton m

end Ctx

namespace I

  def inl {T : Type} {α : T} {Γ : Ctx T} (Δ : Ctx T) (t : I α Γ)
    : I α (Γ ++ Δ)
    := match t with
      | new => new
      | old tail => match Γ with
        | _ :: _ => old (inl Δ tail)

  def inr {T : Type} {α : T} (Γ : Ctx T) {Δ : Ctx T} (t : I α Δ)
    : I α (Γ ++ Δ)
    := match Γ with
      | [] => t
      | _ :: tail => old (inr tail t)
end I

-- def r {X : Familyₛ} {α : T} {Γ : Ctx} (t : X α Γ)
  -- : (Δ : Ctx) → (Ctx.rename Γ Δ) → (X α Δ)
  -- := _


/-- Modal operator (abstracting renaming-dependence) [FS22, Section 2.2.1] -/
def box {T: Type} (X : Familyₛ T) : Familyₛ T
  := λ α Γ => {Δ : Ctx T} → (Ctx.rename Γ Δ) → X α Δ

/-- Box-coalgebra [FS22, Section 2.2.1] -/
structure Coalg {T : Type} (X : Familyₛ T) where
  r : s_family_map X (box X)
  counit
    : {α : T}
    → {Γ : Ctx T}
    → { t : X α Γ}
    → r t id = t
  comult
    : {α : T}
    → {Γ Δ Θ : Ctx T}
    → {ρ₁ : Ctx.rename Γ Δ}
    → {ρ₂ : Ctx.rename Δ Θ}
    → {t : X α Γ}
    → r t (ρ₂ ∘ ρ₁) = r (r t ρ₁) ρ₂

/-- Weakening of context [FS22, Section 2.2.1] -/
def wkl {T : Type} {X : Familyₛ T} (coalg : Coalg X) {α : T} {Γ Δ : Ctx T} (t : X α Γ)
  : X α (Γ ++ Δ)
  := coalg.r t (I.inl Δ)

/-- Weakening of context [FS22, Section 2.2.1] -/
def wkr {T : Type} {X : Familyₛ T} (coalg : Coalg X) {α : T} {Γ Δ : Ctx T} (t : X α Δ)
  : X α (Γ ++ Δ)
  := coalg.r t (I.inr Γ)

/-- Contraction of context [FS22, Section 2.2.1] -/
def contraction {T : Type} {X : Familyₛ T} (coalg : Coalg X) {α : T} {Γ : Ctx T} (t : X α (Γ ++ Γ))
  : X α Γ
  := coalg.r t (Ctx.copair id id)

/-- Homomorphism between box-coalgebras [FS22, Section 2.2.1] -/
structure CoalgHom
  {T : Type}
  {X Y : Familyₛ T}
  (coalg_X : Coalg X)
  (coalg_Y : Coalg Y)
  (f : s_family_map X Y)
where
  homᵣ
    : {α : T}
    → {Γ Δ : Ctx T}
    → {ρ : Ctx.rename Γ Δ}
    → {t : X α Γ}
    → f (coalg_X.r t ρ) = coalg_Y.r (f t) ρ

/-- Pointed box-coalgebras [FS22, Section 2.2.2] -/
structure PointedCoalg {T : Type} (X : Familyₛ T) where
  coalg : Coalg X
  η : s_family_map I X -- coercion of variables into X-terms
  r_η
    : {α : T}
    → {Γ Δ : Ctx T}
    → {v : I α Γ}
    → {ρ : Ctx.rename Γ Δ}
    → coalg.r (η v) ρ = η (ρ v)

/-- Point-preserving homomorphisms [FS22, Section 2.2.2] -/
structure PointedCoalgHom
  {T : Type}
  {X Y : Familyₛ T}
  (p_coalg_X : PointedCoalg X)
  (p_coalg_Y : PointedCoalg Y)
  (f : s_family_map X Y)
where
  coalg_hom : CoalgHom p_coalg_X.coalg p_coalg_Y.coalg f
  hom_η
    : {α : T}
    → {Γ : Ctx T}
    → {v : I α Γ}
    → f (p_coalg_X.η v) = p_coalg_Y.η v

/-- Internal substitution hom of X and Y [FS22, Section 2.2.3] -/
def SubstitutionHom {T: Type} (X : Familyₛ T) (Y : Familyₛ T) : Familyₛ T
 := λ α Γ => {Δ : Ctx T} → (Ctx.map Γ X Δ) → Y α Δ

/-- Substitution tensor product [FS22, Section 2.2.3] -/
def SubstitutionTensorProd {T : Type} (X : Familyₛ T) (Y : Familyₛ T) : Familyₛ T
  := λ α Δ => Σ Γ : Ctx T, X α Γ × Ctx.map Γ Y Δ

/-- Monoid expressed via the internal hom [FS22, Section 2.2.3] -/
structure Mon {T : Type} (M : Familyₛ T) where
  η : s_family_map I M
  μ : s_family_map M (SubstitutionHom M M) -- multiplication; represents simultaneous substitution
  lunit
    : {Γ Δ : Ctx T}
    → {α : T}
    → {σ : Ctx.map Γ M Δ}
    → (v : I α Γ)
    → μ (η v) σ = σ v
  runit
    : {Γ : Ctx T}
    → {α : T}
    → {t : M α Γ}
    → μ t η = t
  assoc
    : {Γ Δ Θ : Ctx T}
    → {α : T}
    → {σ : Ctx.map Γ M Δ}
    → {ζ : Ctx.map Δ M Θ}
    → (t : M α Γ)
    → μ (μ t σ) ζ = μ t (λ v => μ (σ v) ζ)

/-- One-variable substitution [FS22, Section 2.2.3] -/
def subst₁
  {T : Type}
  {α β : T}
  {Γ : Ctx T}
  {M : Familyₛ T}
  (mon : Mon M)
  (s : M α Γ)
  (t : M β (α :: Γ))
  : M β Γ
  := mon.μ t (Ctx.add M s mon.η)

/-- Two-variable substitution [FS22, Section 2.2.3] -/
def subst₂
  {T : Type}
  {α β τ : T}
  {Γ : Ctx T}
  {M : Familyₛ T}
  {mon : Mon M}
  (s₁ : M α Γ)
  (s₂ : M β Γ)
  (t : M τ (α :: β :: Γ))
  : M τ Γ
  := mon.μ t (Ctx.add M s₁ (Ctx.add M s₂ mon.η))

/-- Semantic substitution lemma [FS22, Section 2.2.3] -/
def semantic_substitution_lemma
  {T : Type}
  { M N : Familyₛ T}
  { mon_M : Mon M}
  { mon_N : Mon N}
  {α : T}
  {Γ Δ : Ctx T}
  (σ : Ctx.map Γ M Δ)
  (t : M α Γ)
  (f : s_family_map M N)
  := f (mon_M.μ t σ) = mon_N.μ (f t) (f ∘ σ)

/-- Semantic substitution lemma for single variable [FS22, Section 2.2.3] -/
def sub_lemma
  {T : Type}
  {M N : Familyₛ T}
  {mon_M : Mon M}
  {mon_N : Mon N}
  {α β : T}
  {Γ Δ : Ctx T}
  (σ : Ctx.map Γ M Δ)
  (s : M α Γ)
  (t : M β (α :: Γ))
  (f : s_family_map M N)
  : f (subst₁ mon_M s t) = subst₁ mon_N (f s) (f t)
  -- := f (mon_M.μ t σ) = mon_N.μ (f t) (f ∘ σ)
  := sorry
