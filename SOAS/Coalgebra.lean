import Mathlib.RingTheory.Coalgebra.Basic
import SOAS.Paper

instance : CommSemiring (Familyₛ T) := sorry
instance : AddCommMonoid a := sorry
instance : Module (Familyₛ T) a := sorry

-- what to put instead of a?
instance : CoalgebraStruct (Familyₛ T) a where
  comul := sorry
  counit := sorry

instance : Coalgebra (Familyₛ T) a where
  coassoc := sorry
  rTensor_counit_comp_comul := sorry
  lTensor_counit_comp_comul := sorry
