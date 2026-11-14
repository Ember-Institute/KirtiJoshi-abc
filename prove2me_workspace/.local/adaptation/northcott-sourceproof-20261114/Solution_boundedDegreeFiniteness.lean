import Definitions.Def_TripodNorthcottComposition
import Theorems.Thm_AbcAdaptation_Tripod_northcottFiniteRoots
import Theorems.Thm_AbcAdaptation_Tripod_northcottPolynomialWitness

set_option autoImplicit false
open NumberField Polynomial
open scoped Classical
open AbcAdaptation
open AbcAdaptation.Tripod
open AbcAdaptation.Tripod.Northcott

theorem solution :
    AbcAdaptation.Tripod.BoundedDegreeFiniteness :=
  AbcAdaptation.Tripod.boundedDegreeFiniteness_of_northcott_children
    AbcAdaptation.Tripod.northcottFiniteRoots
    AbcAdaptation.Tripod.northcottPolynomialWitness
