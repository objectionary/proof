import Mathlib.Util.CompileInductive

/-!
# Metatheory about term-rewriting systems

This is an adaptation of [Mathlib.Logic.Relation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html) for `Type`-valued relations (contrary to `Prop`)

-/

set_option autoImplicit false

universe u
variable {α : Type u}
variable {r r1 r2 : α → α → Type u}

/-- Property of being reflexive -/
def Reflexive := ∀ x, r x x

/-- Property of being transitive -/
def Transitive := ∀ x y z, r x y → r y z → r x z

/-- Reflexive transitive closure -/
inductive ReflTransGen (r : α → α → Type u) : α → α → Type u
  | refl {a : α} : ReflTransGen r a a
  | head {a b c : α} : r a b → ReflTransGen r b c → ReflTransGen r a c

compile_inductive% ReflTransGen

namespace ReflTransGen
/-- Rt-closure is transitive -/
def trans {a b c : α} (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  match hab with
  | .refl => by assumption
  | .head x tail => (trans tail hbc).head x

def size {a b : α} (hab : ReflTransGen r a b) : Nat
  := match hab with
    | .refl => 0
    | .head _ tail => 1 + size tail

end ReflTransGen

/-- Two elements can be `join`ed if there exists an element to which both are related -/
def Join (r : α → α → Type u) (a : α) (b : α) : Type u
  := Σ w : α, Prod (r a w) (r b w)

/-- Property that if diverged in 1 step, the results can be joined in 1 step -/
@[simp]
def DiamondProperty (r : α → α → Type u)
  := ∀ a b c, r a b → r a c → Join r b c

/-- Property that if diverged in any number of steps, the results can be joined in any number of steps -/
@[simp]
def Confluence (r : α → α → Type u)
  := ∀ a b c, ReflTransGen r a b → ReflTransGen r a c → Join (ReflTransGen r) b c

def Takahashi (r : α → α → Type u)
  := Σ complete_development : α → α, ∀ {s u}, r s u → r u (complete_development s)

def takahashi_implies_diamond
  (tak : Takahashi r)
  : DiamondProperty r
  := λ a _b _c rab rac =>
    let ⟨cd, joins⟩ := tak
    ⟨cd a, joins rab, joins rac⟩

/-- Diamond property implies Church-Rosser (in the form in which Lean recognizes termination) -/
def diamond_implies_confluence'
  (h : ∀ a b c, r a b → r a c → Join r b c)
  (a b c : α)
  (hab : ReflTransGen r a b)
  (hac : ReflTransGen r a c)
  : Join (ReflTransGen r) b c := match hab with
  | ReflTransGen.refl => ⟨ c, hac,  ReflTransGen.refl⟩
  | ReflTransGen.head hax hxb => by
    let rec step
    { a b c : α }
    (h : ∀ a b c, r a b → r a c → Join r b c)
    (hab : r a b)
    (hac : ReflTransGen r a c)
    : Σ d : α, Prod (ReflTransGen r b d) (r c d) := match hac with
    | ReflTransGen.refl => ⟨ b, ReflTransGen.refl, hab ⟩
    | ReflTransGen.head hax hxc => by
      rename_i x
      have ⟨y, hby, hxy⟩ := (h a b x hab hax)
      have ⟨d, hyd, hcd⟩ := step h hxy hxc
      exact ⟨d, ReflTransGen.head hby hyd, hcd⟩
    rename_i x
    have ⟨c', hxc', hcc'⟩ := step h hax hac
    have ⟨d, hbd, hc'd⟩ := diamond_implies_confluence' h x b c' hxb hxc'
    exact ⟨d, hbd, ReflTransGen.head hcc' hc'd⟩

/-- Diamond property implies Church-Rosser -/
def diamond_implies_confluence : DiamondProperty r → Confluence r := by
  simp
  intros h a b c hab hac
  exact diamond_implies_confluence' h a b c hab hac

def Equivalece (r1 r2 : α → α → Type u)
  := (∀ {a b}, r1 a b → r2 a b) × (∀ {a b}, r2 a b → r1 a b)

def WeakEquivalence (r1 r2 : α → α → Type u)
  := (∀ {a b}, ReflTransGen r1 a b -> ReflTransGen r2 a b) × (∀ {a b}, ReflTransGen r2 a b -> ReflTransGen r1 a b)

def weak_equiv_keeps_confluence
  (weakEquiv : WeakEquivalence r1 r2)
  (conf : Confluence r1)
  : Confluence r2
  := λ a b c r2ab r2ac =>
    let ⟨r1_to_r2, r2_to_r1⟩ := weakEquiv
    let r1ab := r2_to_r1 r2ab
    let r1ac := r2_to_r1 r2ac
    let ⟨w, r1bw, r1cw⟩ := conf a b c r1ab r1ac
    ⟨w, r1_to_r2 r1bw, r1_to_r2 r1cw⟩


@[simp]
def ZProperty (r : α → α → Type u)
  := Σ f : α → α, ∀ {a b}, r a b → ReflTransGen r b (f a) × ReflTransGen r (f a) (f b)


def lift_f
  {a b : α}
  (ab : ReflTransGen r a b)
  (z : ZProperty r)
  : ReflTransGen r (z.fst a) (z.fst b)
  := match ab with
    | .refl => .refl
    | @ReflTransGen.head _ _ _ _u _ au ub =>
      let ⟨_, fa_fu⟩ := z.snd au
      let fu_fb := lift_f ub z
      ReflTransGen.trans fa_fu fu_fb

def aux
  {a b u : α}
  (au : r a u)
  (u_b : ReflTransGen r u b)
  (z : ZProperty r)
  : ReflTransGen r b (z.fst b)
  := match u_b with
    | .refl => let ⟨u_fa, fa_fu⟩ := z.snd au; ReflTransGen.trans u_fa fa_fu
    | @ReflTransGen.head _ _ _ _s _ as sb =>
      aux as sb z

def step
  {a b c : α}
  (ab : r a b)
  (ac : ReflTransGen r a c)
  (z : ZProperty r)
  : ReflTransGen r b (z.fst c)
  := let fa_fc := lift_f ac z
     let b_fa  := (z.snd ab).fst
     ReflTransGen.trans b_fa fa_fc

def decr {a b c} (ab : r a b) (b_c : ReflTransGen r b c)
  : b_c.size < (ReflTransGen.head ab b_c).size
  := match b_c with
  | .refl => by simp [ReflTransGen.size]
  | .head _ tail => by
      simp [ReflTransGen.size]
      let h : tail.size < 1 + tail.size := Nat.lt_add_of_pos_left Nat.zero_lt_one
      exact Nat.add_lt_add_left h 1

def z_confluence
  (z : ZProperty r)
  {a b c : α}
  (a_b : ReflTransGen r a b)
  (a_c : ReflTransGen r a c)
  : Join (ReflTransGen r) b c
  := match hab : a_b with
    | .refl => ⟨c, a_c, .refl⟩
    | .head au u_b => match hac : a_c with
      | .refl => by
        rename_i hb _
        exact ⟨b, .refl, hb ▸ a_b⟩
      | .head as s_c =>
        let u_fc := step au a_c z
        let ⟨w, b_w, fc_w⟩ := z_confluence z u_b u_fc
        by
        rename_i hc
        exact ⟨w, b_w, ReflTransGen.trans (aux as s_c z) (hc ▸ fc_w)⟩
termination_by a_b.size
decreasing_by
  simp_wf
  rename_i as' s_c' _ _ _ _
  exact decr as' s_c'

def z_implies_confluence
  (z : ZProperty r)
  : Confluence r
  := λ _ _ _ ab ac => z_confluence z ab ac
