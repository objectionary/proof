-- SPDX-FileCopyrightText: Copyright (c) 2024-2026 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Minimal.Calculus

open Term
open OptionalAttr
open Reduce

/-!
# Confluence of minimal φ-calculus

This file contains examples of minimal φ-calculus terms and their reductions.

Summary:
1. R_dot, locator substitution:
    ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.x ⇝* ⟦ ⟧
2. R_app, R_dot, cong_DOT:
    ⟦ x ↦ ∅ ⟧(x ↦ ⟦ ⟧).x ⇝* ⟦ ⟧
3. R_dot, locator substitution, cong_DOT:
    ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z ⇝* ⟦ ⟧
4. R_phi:
    ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.x ⇝* ⟦ ⟧
5. cong_APP, R_app, locator increment
    ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ρ⁰.y) ⟧ ⇝* ⟦ x ↦ ⟦ a ↦ ρ¹.y ⟧ ⟧
6. Infinite reduction sequence presented after Definition 3.1 [KS22]
    ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.x ⇝ ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.y
    ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.y ⇝ ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.x
7. Examples/tests of different reductions of the same term presented after Definition 3.1 [KS22]
    ⟦ x ↦ ⟦ y ↦ ∅ ⟧ ⟧.x(y ↦ ⟦ z ↦ w ⟧.z)
8. Locator decrement in substitution, cong_OBJ, R_dot
    ⟦ b ↦ ⟦ c ↦ ρ¹ ⟧.c ⟧ ⇝* ⟦ b ↦ ρ⁰ ⟧
9. R_dot, R_app, cong_OBJ, congAPPₗ
    ⟦ a ↦ ⟦ b ↦ ∅ ⟧ ⟧.a (b ↦ ⟦ ⟧) ⇝* ⟦ b ↦ ⟦ ⟧ ⟧
10. congAPPᵣ, R_dot
    ⟦ ⟧ (a ↦ ⟦ b ↦ ⟦ ⟧ ⟧.b) ⇝* ⟦ ⟧ (a ↦ ⟦ ⟧)

## References

* [Nikolai Kudasov and Violetta Sim. 2023. Formalizing 𝜑-Calculus: A Purely Object-Oriented Calculus of Decorated Objects.][KS22]
-/

-- TEST 1: ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.x ⇝* ⟦ ⟧

-- bindings: x ↦ ρ⁰.y, y ↦ ⟦ ⟧
def bindings1 : Bindings ["x", "y"] :=
  Bindings.cons
    "x"
    (by simp)
    (attached (dot (loc 0) "y"))
    (Bindings.cons
      "y"
      (by simp)
      (attached (obj Bindings.nil))
      Bindings.nil)

-- ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.x
def example1 : Term := dot (obj bindings1) "x"

-- ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.y
def example1_a : Term := dot (obj bindings1) "y"

-- ⟦ ⟧
def example1_res : Term := obj Bindings.nil

-- ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.x ⇝ ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.y
def test1_red1 : example1 ⇝ example1_a := by
  rw [example1, example1_a]
  have := (@dot_c
    (obj bindings1)
    (dot (loc 0) "y")
    "x"
    ["x", "y"]
    (bindings1)
    (by simp [example1])
    (by simp [lookup]))
  simp at this; exact this

-- ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.y ⇝ ⟦ ⟧
def test1_red2 : example1_a ⇝ example1_res := by
  rw [example1_a, example1_res]
  exact (dot_c
    (obj Bindings.nil)
    "y"
    (bindings1)
    rfl
    (by simp [lookup]))

-- ⟦ x ↦ ρ⁰.y, y ↦ ⟦ ⟧ ⟧.x ⇝* ⟦ ⟧
def test1 : example1 ⇝* example1_res :=
  ReflTransGen.head
    test1_red1
    (ReflTransGen.head
      test1_red2
      ReflTransGen.refl)

------------------------------------------
-- TEST 2: ⟦ x ↦ ∅ ⟧(x ↦ ⟦ ⟧).x ⇝* ⟦ ⟧

-- ⟦ x ↦ ∅ ⟧(x ↦ ⟦ ⟧).x
def example2 : Term :=
  dot
    (app
      (obj (Bindings.cons "x" (by simp) void Bindings.nil))
      "x"
      (obj Bindings.nil))
    "x"

-- ⟦ x ↦ ⟦ ⟧ ⟧.x
def example2_a : Term :=
  dot
    (obj
      (Bindings.cons
        "x"
        (by simp)
        (attached (obj Bindings.nil))
        Bindings.nil))
    "x"

-- ⟦ ⟧
def example2_res : Term := obj Bindings.nil

-- ⟦ x ↦ ∅ ⟧(x ↦ ⟦ ⟧).x ⇝ ⟦ x ↦ ⟦ ⟧ ⟧.x
def test2_red1 : example2 ⇝ example2_a := congDOT
  (app
    (obj (Bindings.cons "x" (by simp) void Bindings.nil))
    "x"
    (obj Bindings.nil))
  (obj
    (Bindings.cons
      "x"
      (by simp)
      (attached (obj Bindings.nil))
      Bindings.nil))
  "x"
  (by
    have := app_c
      (obj (Bindings.cons "x" (by simp) void Bindings.nil))
      (obj Bindings.nil)
      "x"
      (Bindings.cons "x" (by simp) void Bindings.nil)
      (by simp)
      (by simp [lookup])
    simp at this; exact this
  )

-- ⟦ x ↦ ⟦ ⟧ ⟧.x ⇝ ⟦ ⟧
def test2_red2 : example2_a ⇝ example2_res := by
  rw [example2_a, example2_res]
  exact (dot_c
    (obj Bindings.nil)
    "x"
    (Bindings.cons
      "x"
      (by simp)
      (attached (obj Bindings.nil))
      Bindings.nil)
    (by simp)
    (by simp [lookup]))

-- ⟦ x ↦ ∅ ⟧(x ↦ ⟦ ⟧).x ⇝* ⟦ ⟧
def test2 : example2 ⇝* example2_res :=
  ReflTransGen.head
    test2_red1
    (ReflTransGen.head
      test2_red2
      ReflTransGen.refl)

------------------------------------------
-- TEST 3: ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z ⇝* ⟦ ⟧

-- ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z
def example3 : Term :=
  dot
    (dot
      (obj
        (Bindings.cons "x" (by simp)
          (attached
            (obj (Bindings.cons "z" (by simp)
              (attached (dot (loc 1) "y"))
              Bindings.nil)))
          (Bindings.cons "y" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)))
      "x")
    "z"

-- ⟦ z ↦ ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.y ⟧.z
def example3_a : Term :=
  dot
    (obj
      (Bindings.cons "z" (by simp)
        (attached
          (dot
            (obj
              (Bindings.cons "x" (by simp)
                (attached (obj
                  (Bindings.cons "z" (by simp)
                    (attached (dot (loc 1) "y"))
                    Bindings.nil
                  )))
                (Bindings.cons "y" (by simp)
                  (attached (obj Bindings.nil))
                  Bindings.nil)))
            "y"))
        Bindings.nil))
    "z"

-- ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.y
def example3_b : Term :=
  dot
    (obj
      (Bindings.cons "x" (by simp)
        (attached (obj
          (Bindings.cons "z" (by simp)
            (attached (dot (loc 1) "y"))
            Bindings.nil
          )))
        (Bindings.cons "y" (by simp)
          (attached (obj Bindings.nil))
          Bindings.nil)))
    "y"

-- ⟦ ⟧
def example3_res : Term := obj Bindings.nil

-- ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z ⇝ ⟦ z ↦ ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.y ⟧.z
def test3_red1 : example3 ⇝ example3_a := congDOT
  (dot
    (obj
      (Bindings.cons "x" (by simp)
        (attached
          (obj (Bindings.cons "z" (by simp)
            (attached (dot (loc 1) "y"))
            Bindings.nil)))
        (Bindings.cons "y" (by simp)
          (attached (obj Bindings.nil))
          Bindings.nil)))
    "x")
  (obj
    (Bindings.cons "z" (by simp)
      (attached
        (dot
          (obj
            (Bindings.cons "x" (by simp)
              (attached (obj
                (Bindings.cons "z" (by simp)
                  (attached (dot (loc 1) "y"))
                  Bindings.nil
                )))
              (Bindings.cons "y" (by simp)
                (attached (obj Bindings.nil))
                Bindings.nil)))
          "y"))
      Bindings.nil))
  "z"
  (by
    have := @dot_c
      (obj
        (Bindings.cons "x" (by simp)
          (attached
            (obj (Bindings.cons "z" (by simp)
              (attached (dot (loc 1) "y"))
              Bindings.nil)))
          (Bindings.cons "y" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)))
      (obj (Bindings.cons "z" (by simp)
        (attached (dot (loc 1) "y"))
        Bindings.nil))
      "x"
      ["x", "y"]
      (Bindings.cons "x" (by simp)
        (attached
          (obj (Bindings.cons "z" (by simp)
            (attached (dot (loc 1) "y"))
            Bindings.nil)))
        (Bindings.cons "y" (by simp)
          (attached (obj Bindings.nil))
          Bindings.nil))
      (by simp)
      (by simp [lookup])
    simp at this; exact this
  )

def test3_red2 : example3_a ⇝ example3_b := by
  simp [example3_a, example3_b]
  have := @dot_c
    (obj
      (Bindings.cons "z" (by simp)
        (attached
          (dot
            (obj
              (Bindings.cons "x" (by simp)
                (attached (obj
                  (Bindings.cons "z" (by simp)
                    (attached (dot (loc 1) "y"))
                    Bindings.nil
                  )))
                (Bindings.cons "y" (by simp)
                  (attached (obj Bindings.nil))
                  Bindings.nil)))
            "y"))
        Bindings.nil))
    (dot
      (obj
        (Bindings.cons "x" (by simp)
          (attached (obj
            (Bindings.cons "z" (by simp)
              (attached (dot (loc 1) "y"))
              Bindings.nil
            )))
          (Bindings.cons "y" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)))
      "y")
    "z"
    ["z"]
    (Bindings.cons "z" (by simp)
        (attached
          (dot
            (obj
              (Bindings.cons "x" (by simp)
                (attached (obj
                  (Bindings.cons "z" (by simp)
                    (attached (dot (loc 1) "y"))
                    Bindings.nil
                  )))
                (Bindings.cons "y" (by simp)
                  (attached (obj Bindings.nil))
                  Bindings.nil)))
            "y"))
        Bindings.nil)
    (by simp)
    (by simp [lookup])
  simp at this; exact this

def test3_red3 : example3_b ⇝ example3_res := by
  rw [example3_b, example3_res]
  exact (dot_c
    (obj Bindings.nil)
    "y"
    (Bindings.cons "x" (by simp)
      (attached (obj
        (Bindings.cons "z" (by simp)
          (attached (dot (loc 1) "y"))
          Bindings.nil
        )))
      (Bindings.cons "y" (by simp)
        (attached (obj Bindings.nil))
        Bindings.nil))
    (by simp)
    (by simp [lookup]))

-- ⟦ x ↦ ⟦ z ↦ ρ¹.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z ⇝* ⟦ ⟧
def test3 : example3 ⇝* example3_res :=
  ReflTransGen.head
    test3_red1
    (ReflTransGen.head
      test3_red2
      ((ReflTransGen.head
        test3_red3
        ReflTransGen.refl)))

------------------------------------------
-- TEST 4: ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.x ⇝* ⟦ ⟧

-- ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.x
def example4 : Term :=
  dot
    (obj
      (Bindings.cons "φ" (by simp)
        (attached
          (obj (Bindings.cons "x" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)))
        Bindings.nil))
    "x"

-- ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.φ.x
def example4_a : Term :=
  dot
    (dot
      (obj
        (Bindings.cons "φ" (by simp)
          (attached
            (obj (Bindings.cons "x" (by simp)
              (attached (obj Bindings.nil))
              Bindings.nil)))
          Bindings.nil))
      "φ")
    "x"

-- ⟦ x ↦ ⟦ ⟧ ⟧.x
def example4_b : Term :=
  dot
    (obj
      (Bindings.cons "x" (by simp)
        (attached (obj Bindings.nil))
        Bindings.nil))
    "x"

-- ⟦ ⟧
def example4_res : Term := obj Bindings.nil

-- ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.x ⇝ ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.φ.x
def test4_red1 : example4 ⇝ example4_a := by
  simp [example4, example4_a]
  have := @dot_cφ
    (obj
      (Bindings.cons "φ" (by simp)
        (attached
          (obj (Bindings.cons "x" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)))
        Bindings.nil))
    "x"
    ["φ"]
    (Bindings.cons "φ" (by simp)
      (attached
        (obj (Bindings.cons "x" (by simp)
          (attached (obj Bindings.nil))
          Bindings.nil)))
      Bindings.nil)
    (by simp)
    (by simp [lookup])
    (by simp)
  simp at this; exact this

-- ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.φ.x ⇝ ⟦ x ↦ ⟦ ⟧ ⟧.x
def test4_red2 : example4_a ⇝ example4_b := congDOT
  (dot
    (obj
      (Bindings.cons "φ" (by simp)
        (attached
          (obj (Bindings.cons "x" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)))
        Bindings.nil))
    "φ")
  (obj
    (Bindings.cons "x" (by simp)
      (attached (obj Bindings.nil))
      Bindings.nil))
  "x"
  (by
    have := @dot_c
      (obj
        (Bindings.cons "φ" (by simp)
          (attached
            (obj (Bindings.cons "x" (by simp)
              (attached (obj Bindings.nil))
              Bindings.nil)))
          Bindings.nil))
      (obj
        (Bindings.cons "x" (by simp)
          (attached (obj Bindings.nil))
          Bindings.nil))
      "φ"
      ["φ"]
      (Bindings.cons "φ" (by simp)
        (attached
          (obj (Bindings.cons "x" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)))
        Bindings.nil)
      (by simp)
      (by simp [lookup])
    simp at this; exact this)

-- ⟦ x ↦ ⟦ ⟧ ⟧.x ⇝ ⟦ ⟧
def test4_red3 : example4_b ⇝ example4_res := by
  rw [example4_b, example4_res]
  exact (dot_c
    (obj Bindings.nil)
    "x"
    (Bindings.cons "x" (by simp)
      (attached (obj Bindings.nil))
      Bindings.nil))
    (by simp)
    (by simp [lookup])

-- ⟦ φ ↦ ⟦ x ↦ ⟦ ⟧ ⟧ ⟧.x ⇝* ⟦ ⟧
def test4 : example4 ⇝* example4_res :=
  ReflTransGen.head
    test4_red1
    (ReflTransGen.head
      test4_red2
      ((ReflTransGen.head
        test4_red3
        ReflTransGen.refl)))

------------------------------------------
-- TEST 5: ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ρ⁰.y) ⟧ ⇝* ⟦ x ↦ ⟦ a ↦ ρ¹.y ⟧ ⟧

-- ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ρ⁰.y) ⟧
def example5 : Term :=
  (obj
    (Bindings.cons "x" (by simp)
      (attached
        (app
          (obj (Bindings.cons "a" (by simp) void Bindings.nil))
          "a"
          (dot (loc 0) "y")))
      Bindings.nil))

-- ⟦ x ↦ ⟦ a ↦ ρ¹.y ⟧ ⟧
def example5_res : Term :=
  (obj
    (Bindings.cons "x" (by simp)
      (attached
        (obj (Bindings.cons "a" (by simp)
          (attached (dot (loc 1) "y"))
          Bindings.nil)))
      Bindings.nil))

-- ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ρ⁰.y) ⟧ ⇝ ⟦ x ↦ ⟦ a ↦ ρ¹.y ⟧ ⟧
def test5_red : example5 ⇝ example5_res := by
  simp [example5, example5_res]
  exact (congOBJ
    "x"
    (Bindings.cons "x" (by simp)
      (attached
        (app
          (obj (Bindings.cons "a" (by simp) void Bindings.nil))
          "a"
          (dot (loc 0) "y")))
      Bindings.nil)
    (by
      have := app_c
        (obj (Bindings.cons "a" (by simp) void Bindings.nil))
        (dot (loc 0) "y")
        "a"
        (Bindings.cons "a" (by simp) void Bindings.nil)
        (by simp)
        (by simp [lookup])
      simp at this; exact this)
    (by apply IsAttached.zeroth_attached))

-- ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ρ⁰.y) ⟧ ⇝* ⟦ x ↦ ⟦ a ↦ ρ¹.y ⟧ ⟧
def test5 : example5 ⇝* example5_res :=
  ReflTransGen.head
    test5_red
    ReflTransGen.refl

---------------------------------
-- TEST 6: infinite reduction sequence presented after Definition 3.1 [KS22]
-- ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.x ⇝ ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.y
-- ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.y ⇝ ⟦ x ↦ ρ⁰.y, y ↦ ρ⁰.x ⟧.x

def example6_bindings : Bindings ["x", "y"] :=
  .cons "x" (by simp) (attached (dot (loc 0) "y"))
  (.cons "y" (by simp) (attached (dot (loc 0) "x")) .nil)

def example6_obj : Term := obj example6_bindings

def test6_1 : (dot example6_obj "x" ⇝ dot example6_obj "y") := by
  have reduction :=
    dot_c
      (dot (loc 0) "y")
      "x"
      example6_bindings
      rfl
      (by simp [lookup])
  simp [substitute] at reduction
  exact reduction

def test6_2 : (dot example6_obj "y" ⇝ dot example6_obj "x") := by
  have reduction :=
    dot_c
      (dot (loc 0) "x")
      "y"
      example6_bindings
      rfl
      (by simp [lookup])
  simp [substitute] at reduction
  exact reduction

---------------------------------
-- Examples/tests of different term reductions presented after Definition 3.1 [KS22]
-- ⟦x ↦ ⟦y ↦ ∅⟧⟧.x(y ↦ ⟦z ↦ w⟧.z)

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

------------------------------------------
-- TEST 8: ⟦ b ↦ ⟦ c ↦ ρ¹ ⟧.c ⟧ ⇝* ⟦ b ↦ ρ⁰ ⟧

-- ⟦ b ↦ ⟦ c ↦ ρ¹ ⟧.c ⟧
def example8 : Term :=
  (obj
    (Bindings.cons "b" (by simp)
      (attached
        (dot
          (obj (Bindings.cons "c" (by simp)
            (attached (loc 1))
            Bindings.nil))
          "c"))
      Bindings.nil))

-- ⟦ b ↦ ρ⁰ ⟧
def example8_res : Term :=
  (obj
    (Bindings.cons "b" (by simp)
      (attached (loc 0))
      Bindings.nil))

-- ⟦ b ↦ ⟦ c ↦ ρ¹ ⟧.c ⟧ ⇝ ⟦ b ↦ ρ⁰ ⟧
def test8_red : example8 ⇝ example8_res := by
  simp [example8, example8_res]
  have := @congOBJ
    (dot
      (obj (Bindings.cons "c" (by simp)
        (attached (loc 1))
        Bindings.nil))
      "c")
    (loc 0)
    "b"
    ["b"]
    (Bindings.cons "b" (by simp)
      (attached
        (dot
          (obj (Bindings.cons "c" (by simp)
            (attached (loc 1))
            Bindings.nil))
          "c"))
      Bindings.nil)
    (by
      have := @dot_c
        (obj (Bindings.cons "c" (by simp)
          (attached (loc 1))
          Bindings.nil))
        (loc 1)
        "c"
        ["c"]
        (Bindings.cons "c" (by simp)
          (attached (loc 1))
          Bindings.nil)
        (by simp)
        (by simp [lookup])
      simp at this; exact this)
    (by apply IsAttached.zeroth_attached)
  simp [insert_φ] at this; exact this

-- ⟦ b ↦ ⟦ c ↦ ρ¹ ⟧.c ⟧ ⇝* ⟦ b ↦ ρ⁰ ⟧
def test8 : example8 ⇝* example8_res :=
  ReflTransGen.head
    test8_red
    ReflTransGen.refl

------------------------------------------
-- TEST 9: ⟦ a ↦ ⟦ b ↦ ∅ ⟧ ⟧.a (b ↦ ⟦ ⟧) ⇝* ⟦ b ↦ ⟦ ⟧ ⟧

-- ⟦ a ↦ ⟦ b ↦ ∅ ⟧ ⟧.a (b ↦ ⟦ ⟧)
def example9 : Term :=
  app
    (dot
      (obj
        (Bindings.cons "a" (by simp)
          (attached (obj
            (Bindings.cons "b" (by simp) void Bindings.nil)))
          Bindings.nil))
      "a")
    "b"
    (obj Bindings.nil)

-- ⟦ b ↦ ∅ ⟧ (b ↦ ⟦ ⟧)
def example9_a : Term :=
  app
    (obj (Bindings.cons "b" (by simp) void Bindings.nil))
    "b"
    (obj Bindings.nil)

-- ⟦ b ↦ ⟦ ⟧ ⟧
def example9_res : Term :=
  (obj
    (Bindings.cons "b" (by simp)
      (attached (obj Bindings.nil))
      Bindings.nil))

-- ⟦ a ↦ ⟦ b ↦ ∅ ⟧ ⟧.a (b ↦ ⟦ ⟧) ⇝ ⟦ b ↦ ∅ ⟧ (b ↦ ⟦ ⟧)
def test9_red1 : example9 ⇝ example9_a := by
  simp [example9, example9_a]
  exact (congAPPₗ _ _ _ _
    (by
      have := @dot_c
        (obj
          (Bindings.cons "a" (by simp)
            (attached (obj
              (Bindings.cons "b" (by simp) void Bindings.nil)))
            Bindings.nil))
        (obj (Bindings.cons "b" (by simp) void Bindings.nil))
        "a"
        ["a"]
        (Bindings.cons "a" (by simp)
          (attached (obj
            (Bindings.cons "b" (by simp) void Bindings.nil)))
          Bindings.nil)
        (by simp)
        (by simp [lookup])
      simp at this; exact this))

-- ⟦ b ↦ ∅ ⟧ (b ↦ ⟦ ⟧) ⇝ ⟦ b ↦ ⟦ ⟧ ⟧
def test9_red2 : example9_a ⇝ example9_res := by
  simp [example9_a, example9_res]
  exact (by
    have := app_c
      (obj (Bindings.cons "b" (by simp) void Bindings.nil))
      (obj Bindings.nil)
      "b"
      (Bindings.cons "b" (by simp) void Bindings.nil)
      (by simp)
      (by simp [lookup])
    simp at this; exact this)

-- ⟦ b ↦ ∅ ⟧ (b ↦ ⟦ ⟧) ⇝* ⟦ b ↦ ⟦ ⟧ ⟧
def test9 : example9 ⇝* example9_res :=
  ReflTransGen.head test9_red1
    (ReflTransGen.head test9_red2
      ReflTransGen.refl)

------------------------------------------
-- TEST 10: ⟦ ⟧ (a ↦ ⟦ b ↦ ⟦ ⟧ ⟧.b) ⇝* ⟦ ⟧ (a ↦ ⟦ ⟧)

-- ⟦ ⟧ (a ↦ ⟦ b ↦ ⟦ ⟧ ⟧.b)
def example10 : Term :=
  app
    (obj Bindings.nil)
    "a"
    (dot
      (obj (Bindings.cons "b" (by simp)
        (attached (obj Bindings.nil))
        Bindings.nil))
      "b")

-- ⟦ ⟧ (a ↦ ⟦ ⟧)
def example10_res : Term :=
  app
    (obj Bindings.nil)
    "a"
    (obj Bindings.nil)

-- ⟦ ⟧ (a ↦ ⟦ b ↦ ⟦ ⟧ ⟧.b) ⇝ ⟦ ⟧ (a ↦ ⟦ ⟧)
def test10_red : example10 ⇝ example10_res := by
  simp [example10, example10_res]
  exact (congAPPᵣ _ _ _ _
    (by
      have := @dot_c
        (obj
          (Bindings.cons "b" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil))
        (obj Bindings.nil)
        "b"
        ["b"]
        (Bindings.cons "b" (by simp)
            (attached (obj Bindings.nil))
            Bindings.nil)
        (by simp)
        (by simp [lookup])
      simp at this; exact this))

-- ⟦ ⟧ (a ↦ ⟦ b ↦ ⟦ ⟧ ⟧.b) ⇝* ⟦ ⟧ (a ↦ ⟦ ⟧)
def test10 : example10 ⇝* example10_res :=
  ReflTransGen.head test10_red
    ReflTransGen.refl
