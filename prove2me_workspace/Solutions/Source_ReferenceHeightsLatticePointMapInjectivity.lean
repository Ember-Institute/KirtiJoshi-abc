import Solutions.Source_ReferenceHeightsLatticePointMap
import Solutions.Source_ReferenceHeightsWeierstrassFibers
import Mathlib.Tactic.LinearCombination

/-!
# Injectivity of the lattice quotient point map

The proof adapts `Heights/LatticePointMapInjectivity.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The affine point constructor is injective
in its two coordinates, so the fiber theorem applies to the actual point map.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open WeierstrassCurve
open scoped UpperHalfPlane Classical

/-- Two complex numbers give the same lattice point exactly when they differ by a period. -/
theorem latticePointMap_eq_iff_sub_mem (τ : ℍ) (z w : ℂ) :
    latticePointMap τ z = latticePointMap τ w ↔ z - w ∈ (periodPair τ).lattice := by
  let L := periodPair τ
  constructor
  · intro heq
    by_cases hz : z ∈ L.lattice
    · by_cases hw : w ∈ L.lattice
      · exact sub_mem hz hw
      · rw [latticePointMap_of_mem (τ := τ) hz,
          latticePointMap_of_notMem (τ := τ) hw] at heq
        exact (Affine.Point.some_ne_zero _ heq.symm).elim
    · by_cases hw : w ∈ L.lattice
      · rw [latticePointMap_of_notMem (τ := τ) hz,
          latticePointMap_of_mem (τ := τ) hw] at heq
        exact (Affine.Point.some_ne_zero _ heq).elim
      · rw [latticePointMap_of_notMem (τ := τ) hz,
          latticePointMap_of_notMem (τ := τ) hw] at heq
        have hcoords := Affine.Point.some.inj heq
        apply (weierstrassP_deriv_eq_iff_sub_mem L z w hz hw).mp
        refine ⟨hcoords.1, ?_⟩
        linear_combination 2 * hcoords.2
  · intro hsub
    have hq : (QuotientAddGroup.mk z : LatticeQuotient τ) = QuotientAddGroup.mk w :=
      QuotientAddGroup.eq_iff_sub_mem.mpr hsub
    simpa only [latticeQuotientPointMap_mk] using congrArg (latticeQuotientPointMap τ) hq

/-- The same Weierstrass point map is injective on the quotient by the period lattice. -/
theorem latticeQuotientPointMap_injective (τ : ℍ) :
    Function.Injective (latticeQuotientPointMap τ) := by
  intro q r heq
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective r
  exact QuotientAddGroup.eq_iff_sub_mem.mpr
    ((latticePointMap_eq_iff_sub_mem τ z w).mp heq)

/-- Additivity and surjectivity of the point map give the uniformization for the torsion bound. -/
theorem latticePointUniformization_of_add_surjective {τ : ℍ}
    (hadd : ∀ z w : ℂ, latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w)
    (hsurj : Function.Surjective (latticeQuotientPointMap τ)) : LatticePointUniformization τ :=
  latticePointUniformization_of_map hadd ⟨latticeQuotientPointMap_injective τ, hsurj⟩

end AbcAdaptation.Reference.Heights
