import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import SOAS.Paper

open CategoryTheory


-- in soas-agda there is a definition of `𝔽amilies` (category of indexed families)
-- and `𝕊orted`, that turns a category into a sorted category
-- https://github.com/DimaSamoz/agda-soas/blob/9f4cca21e3e80ae35ec1b796e3f49b8a3e64ccbe/SOAS/Families/Core.agda
-- https://github.com/DimaSamoz/agda-soas/blob/9f4cca21e3e80ae35ec1b796e3f49b8a3e64ccbe/SOAS/Sorting.agda

instance : CategoryStruct (Familyₛ T) where
  Hom := s_family_map
  id := λ _ => id
  comp := λ {C1 C2 C3} (r1 : s_family_map C1 C2) (r2 : s_family_map C2 C3) => r2 ∘ r1

instance 𝔽amiliesₛ : Category (Familyₛ T) where
  id_comp := by aesop_cat
  comp_id := by aesop_cat
  assoc := by aesop_cat

-- A bicartesian closed category is a cartesian closed category with finite coproducts

def limitCone (F : Discrete (Fin n) ⥤ Familyₛ T) : Limits.LimitCone F where
  cone := sorry
  isLimit := sorry

def colimitCone (F : Discrete (Fin n) ⥤ Familyₛ T) : Limits.ColimitCocone F where
  cocone := sorry
  isColimit := sorry

instance (F : Discrete (Fin n) ⥤ Familyₛ T) : Limits.HasLimit F where
  exists_limit := Nonempty.intro (limitCone F)

instance (F : Discrete (Fin n) ⥤ Familyₛ T) : Limits.HasColimit F where
  exists_colimit := Nonempty.intro (colimitCone F)

instance (n : ℕ) : Limits.HasLimitsOfShape (Discrete (Fin n)) (Familyₛ T) where
instance (n : ℕ) : Limits.HasColimitsOfShape (Discrete (Fin n)) (Familyₛ T) where

instance : Limits.HasFiniteProducts (Familyₛ T) where
  out := fun n => by infer_instance

instance : MonoidalCategory (Familyₛ T) := sorry -- where
  -- tensorObj := sorry
  -- whiskerLeft := sorry
  -- whiskerRight := sorry
  -- tensorUnit := sorry
  -- associator := sorry
  -- leftUnitor := sorry
  -- rightUnitor := sorry

instance : CartesianClosed (Familyₛ T) := sorry

instance : Limits.HasFiniteCoproducts (Familyₛ T) where
  out := fun n => by infer_instance
