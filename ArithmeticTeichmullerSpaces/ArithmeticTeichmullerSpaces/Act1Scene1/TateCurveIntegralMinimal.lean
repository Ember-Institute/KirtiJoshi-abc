import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.ReductionNorm

/-!
source-id: JT-SCENE1-ACTUAL-TATE-CURVE-MINIMALITY
source: Silverman's minimal-Weierstrass criterion as used by Mathlib's
`WeierstrassCurve.IsMinimal`; Joshi III `ss:val-sets-defn`.
fidelity: proves that an integral Weierstrass equation with unit c4 is
minimal by comparing its discriminant valuation with every integral
variable change. This is a local model criterion, not a global reduction
classification.
boundary: Scene1/Derived. No Prologue boundary or parent checkbox changes.
-/

namespace JoshiTeich.Act1Scene1.TateReduction

open WeierstrassCurve IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
open JoshiTeich.ReferenceIut

noncomputable section

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral Weierstrass equation with unit `c4` is minimal over the DVR. -/
lemma isMinimal_of_integral_c₄_unit (W : WeierstrassCurve K)
    [W.IsIntegral R]
    (hc₄ : valuation K (maximalIdeal R) W.c₄ = 1) : W.IsMinimal R := by
  let v := valuation K (maximalIdeal R)
  refine ⟨⟨by simpa only [one_smul] using (inferInstance : W.IsIntegral R), ?_⟩⟩
  intro C hC _
  letI : (C • W).IsIntegral R := hC
  have hC₄ : v (C • W).c₄ ≤ 1 := by
    rw [← integralModel_c₄_eq R (C • W)]
    exact valuation_le_one (maximalIdeal R) _
  have hu4 : v (↑(C.u⁻¹) : K) ^ 4 ≤ 1 := by
    have h := hC₄
    rw [variableChange_c₄, map_mul, map_pow, hc₄, mul_one] at h
    exact h
  have hu : v (↑(C.u⁻¹) : K) ≤ 1 :=
    (pow_le_one_iff_of_nonneg zero_le (by decide : (4 : ℕ) ≠ 0)).mp hu4
  have hu12 : v (↑(C.u⁻¹) : K) ^ 12 ≤ 1 :=
    pow_le_one₀ zero_le hu
  have hΔ : v (C • W).Δ ≤ v W.Δ := by
    rw [variableChange_Δ, map_mul, map_pow]
    exact (mul_le_mul_of_nonneg_right hu12 zero_le).trans_eq (one_mul _)
  change (valuation_Δ_aux R (C • W)).val ≤
    (valuation_Δ_aux R ((1 : VariableChange K) • W)).val
  rw [valuation_Δ_aux_eq_of_isIntegral, one_smul, valuation_Δ_aux_eq_of_isIntegral]
  exact hΔ

end
end JoshiTeich.Act1Scene1.TateReduction
