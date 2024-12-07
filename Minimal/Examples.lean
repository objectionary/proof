import Minimal.Calculus

open Term
open OptionalAttr
open Reduce

-- TEST 1: ⟦ x ↦ ξ.y, y ↦ ⟦ ⟧ ⟧.x ⇝* ⟦ ⟧

-- bindings: x ↦ ξ.y, y ↦ ⟦ ⟧
def bindings1 : Bindings ["x", "y"] :=
  Bindings.cons
    "x"
    (by simp)
    (attached (dot (loc 0) "y"))
    (Bindings.cons
      "y"
      (by simp)
      (attached (obj (Bindings.nil)))
      Bindings.nil)

-- ⟦ x ↦ ξ.y, y ↦ ⟦ ⟧ ⟧.x
def example1 : Term := dot (obj bindings1) "x"

-- ⟦ x ↦ ξ.y, y ↦ ⟦ ⟧ ⟧.y
def example1_a : Term := dot (obj bindings1) "y"

-- ⟦ ⟧
def example1_res : Term := obj Bindings.nil

-- ⟦ x ↦ ξ.y, y ↦ ⟦ ⟧ ⟧.x ⇝ ⟦ x ↦ ξ.y, y ↦ ⟦ ⟧ ⟧.y
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

-- ⟦ x ↦ ξ.y, y ↦ ⟦ ⟧ ⟧.y ⇝ ⟦ ⟧
def test1_red2 : example1_a ⇝ example1_res := by
  rw [example1_a, example1_res]
  exact (dot_c
    (obj Bindings.nil)
    "y"
    (bindings1)
    rfl
    (by simp [lookup]))

-- ⟦ x ↦ ξ.y, y ↦ ⟦ ⟧ ⟧.x ⇝* ⟦ ⟧
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
      (attached (obj (Bindings.nil)))
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
-- TEST 3: ⟦ x ↦ ⟦ z ↦ ρ.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z ⇝* ⟦ ⟧

-- ⟦ x ↦ ⟦ z ↦ ρ.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z
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

-- ⟦ z ↦ ⟦ x ↦ ⟦ z ↦ ρ.y ⟧, y ↦ ⟦ ⟧ ⟧.y ⟧.z
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

-- ⟦ x ↦ ⟦ z ↦ ρ.y ⟧, y ↦ ⟦ ⟧ ⟧.y
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

-- ⟦ x ↦ ⟦ z ↦ ρ.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z ⇝ ⟦ z ↦ ⟦ x ↦ ⟦ z ↦ ρ.y ⟧, y ↦ ⟦ ⟧ ⟧.y ⟧.z
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

-- ⟦ x ↦ ⟦ z ↦ ρ.y ⟧, y ↦ ⟦ ⟧ ⟧.x.z ⇝* ⟦ ⟧
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
-- TEST 5: ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ξ.y) ⟧ ⇝* ⟦ x ↦ ⟦ a ↦ ρ.y ⟧ ⟧

-- ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ξ.y) ⟧
def example5 : Term :=
  (obj
    (Bindings.cons "x" (by simp)
      (attached
        (app
          (obj (Bindings.cons "a" (by simp) void Bindings.nil))
          "a"
          (dot (loc 0) "y")))
      Bindings.nil))

-- ⟦ x ↦ ⟦ a ↦ ρ.y ⟧ ⟧
def example5_res : Term :=
  (obj
    (Bindings.cons "x" (by simp)
      (attached
        (obj (Bindings.cons "a" (by simp)
          (attached (dot (loc 1) "y"))
          Bindings.nil)))
      Bindings.nil))

-- ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ξ.y) ⟧ ⇝ ⟦ x ↦ ⟦ a ↦ ρ.y ⟧ ⟧
def test5_red : example5 ⇝ example5_res := by
  simp [example5, example5_res]
  exact (@congOBJ
    (app
      (obj (Bindings.cons "a" (by simp) void Bindings.nil))
      "a"
      (dot (loc 0) "y"))
    (obj (Bindings.cons "a" (by simp)
      (attached (dot (loc 1) "y"))
      Bindings.nil))
    "x"
    ["x"]
    (Bindings.cons "x" (by simp)
      (attached
        (app
          (obj (Bindings.cons "a" (by simp) void Bindings.nil))
          "a"
          (dot (loc 0) "y")))
      Bindings.nil)
    (by
      have := @app_c
        (obj (Bindings.cons "a" (by simp) void Bindings.nil))
        (dot (loc 0) "y")
        "a"
        ["a"]
        (Bindings.cons "a" (by simp) void Bindings.nil)
        (by simp)
        (by simp [lookup])
      simp at this; exact this)
    (by apply IsAttached.zeroth_attached))

-- ⟦ x ↦ ⟦ a ↦ ∅ ⟧ (a ↦ ξ.y) ⟧ ⇝* ⟦ x ↦ ⟦ a ↦ ρ.y ⟧ ⟧
def test5 : example5 ⇝* example5_res :=
  ReflTransGen.head
    test5_red
    ReflTransGen.refl
