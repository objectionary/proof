import Minimal.Calculus

open Term
open OptionalAttr
open Reduce

-- ⟦ a ↦ ⟦ ⟧ ⟧.a
def example1 : Term :=
  dot
    (obj
      (Bindings.cons
        "a"
        (by simp)
        (attached (obj (Bindings.nil)))
        Bindings.nil))
    "a"

-- ⟦ ⟧
def example1' : Term := obj Bindings.nil

-- ⟦ a ↦ ⟦ ⟧ ⟧.a ⇝ ⟦ ⟧
def test1_red1 : example1 ⇝ example1' := by
  rw [example1, example1']
  exact (dot_c
    (obj Bindings.nil)
    "a"
    (Bindings.cons
      "a"
      (by simp)
      (attached (obj (Bindings.nil)))
      Bindings.nil)
    (by simp)
    (by simp [lookup]))

-- ⟦ a ↦ ⟦ ⟧ ⟧.a ⇝* ⟦ ⟧
def test1 : example1 ⇝* example1' := ReflTransGen.head
  test1_red1
  ReflTransGen.refl
