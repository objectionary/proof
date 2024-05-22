import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import SOAS.Paper

open CategoryTheory
variable (T : Type)

-- https://github.com/DimaSamoz/agda-soas/blob/9f4cca21e3e80ae35ec1b796e3f49b8a3e64ccbe/SOAS/ContextMaps/CategoryOfRenamings.agda#L22
instance : CategoryStruct (Ctx T) where
  Hom := Ctx.rename
  id := λ _ => id
  comp := λ {C1 C2 C3} (r1 : Ctx.rename C1 C2) (r2 : Ctx.rename C2 C3) => r2 ∘ r1

instance 𝔽 : Category (Ctx T) where
  id_comp := by aesop_cat
  comp_id := by aesop_cat
  assoc := by aesop_cat

def colimitCocone (F : Discrete Limits.WalkingPair ⥤ Ctx T) : Limits.ColimitCocone F
  := {
    cocone := {
      pt := sorry,
      ι := sorry
    }
    isColimit := {
      desc := sorry
      fac := sorry
      uniq := sorry
    }
  }

instance hasColimitF
  (F : Discrete Limits.WalkingPair ⥤ Ctx T): Limits.HasColimit F where
  exists_colimit := Nonempty.intro (colimitCocone T F)

instance boo : Limits.HasColimitsOfShape (Discrete Limits.WalkingPair) (Ctx T) where
  has_colimit : ∀ F, Limits.HasColimit F := by infer_instance

-- is it same as cocartesian?
instance : Limits.HasBinaryCoproducts (Ctx T) where
