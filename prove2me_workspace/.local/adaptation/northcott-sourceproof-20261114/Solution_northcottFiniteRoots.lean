import Definitions.Def_TripodNorthcottInputs

set_option autoImplicit false
open NumberField Polynomial
open scoped Classical
open AbcAdaptation
open AbcAdaptation.Tripod
open AbcAdaptation.Tripod.Northcott

/-- Source proof of `Iut.Tripod.finite_roots_polySet` (line 150), directly
using Mathlib's finite-coefficient polynomial-root union theorem. -/
theorem solution : Northcott.FiniteRoots := by
  intro d H
  exact bUnion_roots_finite (Int.castRingHom Qbar) d (Set.finite_Icc _ _)
