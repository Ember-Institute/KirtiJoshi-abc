/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors

Adapted from Genl/Curves/BelyiDescent.lean:127-139 at
 ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf.
The source concludes (1 - φ)⁻¹ is regular; this consumer needs (φ - 1)⁻¹.
-/
import Definitions.Def_FermatLocalBelyi
import Definitions.Def_FermatCurveFieldResidue

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem avoidanceRegularity {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M) :
    AvoidanceRegularity M hDVR := by
  letI : IsCurveField M.K := M.isCurveField
  intro φ P hP
  change ¬ (ord M hDVR P φ ≠ 0 ∨ 0 < ord M hDVR P (φ - 1)) at hP
  simp only [ord_eq_placeOrd, not_or, not_lt, not_not] at hP
  obtain ⟨hc0, hc1⟩ := hP
  have hm : φ ∈ P.1 := P.mem_of_ord_nonneg hc0.ge
  have hm1 : φ - 1 ∈ P.1 := sub_mem hm P.1.one_mem
  have h1' := P.ord_nonneg_of_mem hm1
  refine ⟨hm, P.mem_of_ord_nonneg ?_, P.mem_of_ord_nonneg ?_⟩
  · rw [Place.ord_inv]
    omega
  · rw [Place.ord_inv]
    omega

end AbcAdaptation.Tripod.Fermat.Proper
