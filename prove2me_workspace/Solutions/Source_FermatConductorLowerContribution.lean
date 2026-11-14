/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/
import Solutions.Source_FermatConductorLowerMultiplicity

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal]

/-- The summands of `diffContrib` in terms of `ord_P(𝔇)` and `f(P|𝔭)`. -/
lemma diffContrib_eq (h𝔭 : 𝔭 ≠ ⊥) :
    diffContrib L 𝔭 = ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
      (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) * 𝔭.inertiaDeg' P *
        Real.log (Ideal.absNorm 𝔭) / finrank ℚ L := by
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  rw [log_absNorm_eq_inertiaDeg_mul h𝔭 P, mul_assoc]

/-- **(a) The lower bound**: `∑_{P ∣ 𝔭} (e − 1)·f·log N(𝔭)/[L : ℚ] ≤ diffContrib L 𝔭`. -/
theorem sum_le_diffContrib (h𝔭 : 𝔭 ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
      ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) * 𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) /
        finrank ℚ L ≤ diffContrib L 𝔭 := by
  rw [diffContrib_eq h𝔭]
  refine Finset.sum_le_sum fun P hP => ?_
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ?_ (by positivity)) (Real.log_natCast_nonneg _)) (by positivity)
  exact_mod_cast ramificationIdx'_sub_one_le_multiplicity h𝔭 P

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource
