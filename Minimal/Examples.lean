import Minimal.Calculus

open Term
open OptionalAttr
open Reduce

/-!
# Confluence of minimal φ-calculus

This file contains examples of minimal φ-calculus terms and their reductions.

## References

* [Nikolai Kudasov and Violetta Sim. 2023. Formalizing 𝜑-Calculus: A Purely Object-Oriented Calculus of Decorated Objects.][KS22]
-/


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

/-- Examples/tests of different term reductions presented after Definition 3.1 [KS22]
⟦x ↦ ⟦y ↦ ∅⟧⟧.x(y ↦ ⟦z ↦ w⟧.z)
-/
def w : Term := obj Bindings.nil
def example_graph_init : Term :=
  app
    (dot
      (obj
        (.cons "x" (by simp) (attached (obj (.cons "y" (by simp) void .nil))) .nil)
      )
      "x"
    )
    "y"
    (dot (obj (.cons "z" (by simp) (attached w) .nil)) "z")

def example_graph_l1 : Term :=
  app
    (obj (.cons "y" (by simp) void .nil))
    "y"
    (dot (obj (.cons "z" (by simp) (attached w) .nil)) "z")
def example_graph_r1 : Term :=
  app
    (dot
      (obj
        (.cons "x" (by simp) (attached (obj (.cons "y" (by simp) void .nil))) .nil)
      )
      "x"
    )
    "y"
    w
def example_graph_l2 : Term :=
  obj
    (.cons "y" (by simp)
      (attached (dot (obj (.cons "z" (by simp) (attached w) .nil)) "z")) .nil
    )
def example_graph_r2 : Term :=
  app
    (obj (.cons "y" (by simp) void .nil))
    "y"
    w
def example_graph_last : Term :=
  obj (.cons "y" (by simp) (attached w) .nil)

def test_graph_1 : example_graph_init ⇝ example_graph_l1
  := congAPPₗ _ _ _ _
    (by
      have reduction := dot_c
        (obj (.cons "y" (by simp) void .nil))
        "x"
        (.cons "x" (by simp) (attached (obj (.cons "y" (by simp) void .nil))) .nil)
        rfl
        (by simp [lookup])
      simp [substitute] at reduction
      exact reduction
    )
def test_graph_2 : example_graph_init ⇝ example_graph_r1
  := congAPPᵣ _ _ _ _
    (by
      have reduction := dot_c
        w
        "z"
        (.cons "z" (by simp) (attached w) .nil)
        rfl
        (by simp [lookup])
      simp [substitute] at reduction
      exact reduction
    )
def test_graph_3 : example_graph_l1 ⇝ example_graph_l2
  := by
    have reduction := app_c
      (obj (.cons "y" (by simp) void .nil))
      (dot (obj (.cons "z" (by simp) (attached w) .nil)) "z")
      "y"
      (.cons "y" (by simp) void .nil)
      rfl
      (by simp [lookup])
    simp [insert_φ] at reduction
    exact reduction
def test_graph_4 : example_graph_l1 ⇝ example_graph_r2
  := congAPPᵣ _ _ _ _
    (by
      have reduction := dot_c
        w
        "z"
        (.cons "z" (by simp) (attached w) .nil)
        rfl
        (by simp [lookup])
      simp [substitute] at reduction
      exact reduction
    )
def test_graph_5 : example_graph_r1 ⇝ example_graph_r2
  := congAPPₗ _ _ _ _
    (by
      have reduction := dot_c
        (obj (.cons "y" (by simp) void .nil))
        "x"
        (.cons "x" (by simp) (attached (obj (.cons "y" (by simp) void .nil))) .nil)
        rfl
        (by simp [lookup])
      simp [substitute] at reduction
      exact reduction
    )
def test_graph_6 : example_graph_l2 ⇝ example_graph_last
  := by
    have reduction := congOBJ
      "y"
      (.cons "y" (by simp)
        (attached (dot (obj (.cons "z" (by simp) (attached w) .nil)) "z"))
        .nil
      )
      (by
        have reduction := dot_c
          w
          "z"
          (.cons "z" (by simp) (attached w) .nil)
          rfl
          (by simp [lookup])
        simp [substitute] at reduction
        exact reduction
      )
      (.zeroth_attached _ _ _ _)
    simp [insert_φ] at reduction
    exact reduction
def test_graph_7 : example_graph_r2 ⇝ example_graph_last
  := by
    have reduction := app_c
      (obj (.cons "y" (by simp) void .nil))
      w
      "y"
      (.cons "y" (by simp) void .nil)
      rfl
      (by simp [lookup])
    simp [insert_φ] at reduction
    exact reduction
