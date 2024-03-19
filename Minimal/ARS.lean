/-!
# Metatheory about term-rewriting systems

This is an adaptation of [Mathlib.Logic.Relation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html) for `Type`-valued relations (contrary to `Prop`)

-/

set_option autoImplicit false

universe u
variable {α : Type u}
variable {r : α → α → Type u}

/-- Property of being reflexive -/
def Reflexive := ∀ x, r x x

/-- Property of being transitive -/
def Transitive := ∀ x y z, r x y → r y z → r x z

/-- Reflexive transitive closure -/
inductive ReflTransGen (r : α → α → Type u) : α → α → Type u
  | refl {a : α} : ReflTransGen r a a
  | head {a b c : α} : r a b → ReflTransGen r b c → ReflTransGen r a c

namespace ReflTransGen
/-- Rt-closure is transitive -/
def trans {a b c : α} (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  match hab with
  | .refl => by assumption
  | .head x tail => (trans tail hbc).head x

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
