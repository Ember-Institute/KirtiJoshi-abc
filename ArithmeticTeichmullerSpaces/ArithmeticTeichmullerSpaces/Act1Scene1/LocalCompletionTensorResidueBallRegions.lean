import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarResidueRegion

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-RESIDUE-BALL-REGIONS
source: actual residue spectral norm integrality criterion and exact
componentwise principal-region decomposition; Joshi III 3568--3574.
fidelity: identifies normalization and scalar normalization regions by
residue norm inequalities in both directions. No arbitrary-set least hull,
paper norm convention, different untilt or theta-locus identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance ballRegionIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem mem_normalization_iff_residueNorm_le_one (x : P.Tensor) :
    x ∈ P.normalization ↔ ∀ I : MaximalSpectrum P.Tensor,
      P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) ≤ 1 := by
  change IsIntegral ℤ_[p] x ↔ _
  rw [P.isIntegral_iff_residue_integral]
  exact forall_congr' fun I => P.isIntegral_iff_residueNorm_le_one I _

theorem mem_scalarNormalization_iff_residueNorm_le_multiplier
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (x : P.Tensor) :
    x ∈ P.scalarNormalization z hz ↔ ∀ I : MaximalSpectrum P.Tensor,
      P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) ≤
        P.residueNorm I (P.scalarResidueMultiplier z I) := by
  rw [P.mem_scalarNormalization_iff_residue_principal z hz x]
  apply forall_congr'
  intro I
  constructor
  · rintro ⟨b, hb, hbx⟩
    rw [← hbx, P.residueNorm_mul]
    exact mul_le_of_le_one_right (P.residueNorm_nonneg I _)
      ((P.isIntegral_iff_residueNorm_le_one I b).mp hb)
  · intro hx
    let a := P.scalarResidueMultiplier z I
    have ha : a ≠ 0 := P.scalarResidueMultiplier_ne_zero z hz I
    have hpos : 0 < P.residueNorm I a := P.residueNorm_pos I ha
    refine ⟨a⁻¹ * Ideal.Quotient.mk I.asIdeal x, ?_, mul_inv_cancel_left₀ ha _⟩
    apply (P.isIntegral_iff_residueNorm_le_one I _).mpr
    rw [P.residueNorm_mul, P.residueNorm_inv]
    calc
      _ ≤ (P.residueNorm I a)⁻¹ * P.residueNorm I a :=
        mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
