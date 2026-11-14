/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/
import Solutions.Source_FermatConductorLowerContribution
import Solutions.Source_FermatConductorPlaceDegree

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

lemma finrank_ℚ_pos (K : Type*) [Field K] [NumberField K] : (0 : ℝ) < finrank ℚ K := by
  exact_mod_cast finrank_pos

section Local

variable {F : Type*} [Field F] [NumberField F] (L : Type*) [Field L] [NumberField L]
  [Algebra F L]

/-- **The local comparison at a place `u` of `F`**:
`log N(u)/[F : ℚ] ≤ ∑_{w ∣ u} log N(w)/[L : ℚ] + diffContrib L u`. -/
theorem log_placeNorm_div_le (u : FinitePlace F) :
    Real.log (placeNorm u) / finrank ℚ F ≤
      ∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L +
        diffContrib L u.maximalIdeal.asIdeal := by
  haveI := u.maximalIdeal.isMaximal
  set 𝔭 := u.maximalIdeal.asIdeal
  have hsum := sum_placesOver_mul_eq_finrank (L := L) u
  have hF := finrank_ℚ_pos F
  have hFL : (0 : ℝ) < finrank F L := by exact_mod_cast finrank_pos
  calc Real.log (placeNorm u) / finrank ℚ F
      = ∑ w ∈ placesOver L u, ((placeRamIdx w u * placeInertiaDeg w u : ℕ) : ℝ) *
          (Real.log (placeNorm u) / finrank ℚ L) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, hsum, ← finrank_mul_finrank ℚ F L, Nat.cast_mul]
        field_simp
    _ = ∑ w ∈ placesOver L u, (Real.log (placeNorm w) / finrank ℚ L +
          ((𝔭.ramificationIdx' w.maximalIdeal.asIdeal - 1 : ℕ) : ℝ) *
            𝔭.inertiaDeg' w.maximalIdeal.asIdeal * Real.log (Ideal.absNorm 𝔭) /
              finrank ℚ L) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have h := mem_placesOver.mp hw
        have he : 1 ≤ placeRamIdx w u := Nat.one_le_iff_ne_zero.mpr (placeRamIdx_ne_zero h)
        rw [log_placeNorm_eq h, Nat.cast_sub he]
        simp only [placeRamIdx, placeInertiaDeg, placeNorm, Nat.cast_mul, Nat.cast_one]
        ring
    _ = ∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L +
          ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
            ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) * 𝔭.inertiaDeg' P *
              Real.log (Ideal.absNorm 𝔭) / finrank ℚ L := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact sum_placesOver_eq u (fun P => ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) *
          𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) / finrank ℚ L)
    _ ≤ _ := add_le_add le_rfl (sum_le_diffContrib u.maximalIdeal.ne_bot)

end Local

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource
