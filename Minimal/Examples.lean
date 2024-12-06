import Minimal.Calculus

open Term
open OptionalAttr
open Reduce

/-
## References

* [Nikolai Kudasov and Violetta Sim. 2023. Formalizing 𝜑-Calculus: A Purely Object-Oriented Calculus of Decorated Objects.][KS22]

Class-based OOP example, modelling the following snippet (Java):

class Base {
  Integer g() { return h(); }
  Integer h() { return 3; }
}
class Derived extends Base {
  Integer f() { return 2 + this.g(); }
  Integer h() { return 5; }
}
Derived d = new Derived();
-/

/-- [KS22, Example 2.8]-/
def base : Term :=
  obj (Bindings.cons
      "new"
      (by simp)
      (attached
        (Bindings.cons
        "g"
        (by simp)
        (attached
          (Bindings.cons
          "this"
          (by simp)
          void
          (Bindings.cons
          "φ"
          (by simp)
          (attached
            (dot
              (app
                (dot
                  (dot
                    (loc 0)
                    "this"
                  )
                  "h"
                )
                "this"
                (dot (loc 0) "this")
              )
              "φ"
            )
          )
          Bindings.nil
          )
          )
        )

        (Binding.cons
        "h"
        (by simp)
        (attached
          (Bindings.cons
          "this"
          (by simp)
          void
          (Bindings.cons
          "φ"
          (by simp)
          (attached (obj (Bindings.cons "3" (by simp) void Bindings.nil))) -- the base calculus does not have numbers, should be a 3
          Bindings.nil
          )
          )
        )
        Bindings.nil
        )
        )
      )
      Binding.nil
      )

def derived : Term :=
  obj (Bindings.cons
      "new"
      (by simp)
      (attached (obj
        (Bindings.cons
        "φ"
        (by simp)
        (attached
          (dot base "new")
        )

        (Binding.cons
        "f"
        (by simp)
        (attached
          (Bindings.cons
          "this"
          (by simp)
          void
          (Bindings.cons
          "φ"
          (by simp)
          (attached
            (app
              (dot
                (obj (Bindings.cons "2" (by simp) void Bindings.nil)) -- the base calculus does not have numbers, should be a 2
                "add"
              )
              "n"
              (dot
                (app
                  (dot
                    (dot
                      (loc 0)
                      "this"
                    )
                    "g"
                  )
                  "this"
                  (dot
                    (loc 0)
                    "this"
                  )
                )
                "φ"
              )
            )
          )
          Bindings.nil
          )
          )
        )

        (Bindings.cons
        "h"
        (by simp)
        (attached
          (Bindings.cons
          "this"
          (by simp)
          void
          (Bindings.cons
          "φ"
          (by simp)
          (attached (obj (Bindings.cons "5" (by simp) void Bindings.nil))) -- the base calculus does not have numbers, should be a 5
          Bindings.nil
          )
          )
        )
        Bindings.nil
        )
        )
        ))
      )
      Binding.nil
      )

def d : Term := dot derived "new"

def invocation1
  : d
  ⇝
  (obj  (Bindings.cons "φ" (by simp) (attached (dot base "new"))
        (Binding.cons "f" (by simp) (attached
          (Bindings.cons "this" (by simp) void
          (Bindings.cons "φ" (by simp) (attached
            (app
              (dot (obj (Bindings.cons "2" (by simp) void Bindings.nil)) "add")
              "n"
              (dot (app (dot (dot (loc 0) "this") "g") "this" (dot (loc 0) "this")) "φ")
            )
          )
          Bindings.nil))
        )
        (Bindings.cons "h" (by simp) (attached
          (Bindings.cons "this" (by simp) void
          (Bindings.cons "φ" (by simp) (attached (obj (Bindings.cons "5" (by simp) void Bindings.nil)))
          Bindings.nil))
        )
        Bindings.nil))
        )
  )
  := by
    simp [substitute]
    exact dot_c _ "new" _ (by simp) (by simp [lookup])

-- def invocation
--   : dot (app (dot d "f") "this" d) "φ" -- d.f(this ↦ d).φ     === Derived.new.f(this ↦ d).φ
--   ⇝* app
--         (dot (obj (Bindings.cons "2" (by simp) void Bindings.nil)) "add")
--         "n"
--         (dot (app (dot d "g") "this" d) "φ")
--   :=
--     ReflTransGen.head
--     (dot_c _ "new" _ _ _)
--     (ReflTransGen.head
--     _
--     (ReflTransGen.head
--     _
--     (ReflTransGen.head
--     _
--     (ReflTransGen.head
--     _
--     (ReflTransGen.head
--     _
--     ReflTransGen.refl
--     )))))


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
