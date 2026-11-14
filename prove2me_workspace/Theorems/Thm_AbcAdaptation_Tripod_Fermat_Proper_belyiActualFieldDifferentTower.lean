/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; validation and source mappings are recorded with this unit.
-/
import Definitions.Def_FermatBelyiDifferentConductorChildren

set_option autoImplicit false
open NumberField Module
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Source Heights/Different/NumberField.lean:53-74; proof-body reuse. -/
private theorem differentConductor_logDisc_tower
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] :
    Real.log |(discr L : ℝ)| / finrank ℚ L =
      Real.log |(discr F : ℝ)| / finrank ℚ F +
        Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := F) (𝒪 := 𝓞 F) (L := L) (𝒪' := 𝓞 L)
  have hD : Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr differentIdeal_ne_bot
  have hF : (discr F).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero F)
  have hFL : (finrank F L : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  rw [← Int.cast_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ← Nat.cast_natAbs, h, Nat.cast_mul,
    Nat.cast_pow, Real.log_mul (by exact_mod_cast hD)
    (by positivity), Real.log_pow, ← finrank_mul_finrank ℚ F L, Nat.cast_mul, add_div,
    add_comm]
  congr 1
  rw [mul_comm ((finrank F L : ℕ) : ℝ), mul_div_mul_right _ _ hFL]

/-- The image field need not equal the full field. No degree equality is assumed. -/
theorem belyiActualFieldDifferentTower : BelyiActualFieldDifferentTower := by
  intro N M hRF φ x hgood
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
    (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
  simpa only [pointLogDiff, Tripod.logDiff, Tripod.deg_eq_finrank,
    belyiRelativeLogDifferent, QbarPoint.degree] using
    differentConductor_logDisc_tower (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf

end AbcAdaptation.Tripod.Fermat.Proper
