import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPositivePilotIntegralTensor
import ArithmeticTeichmullerSpaces.Act1Scene1.ThetaWitnessProduct

/-!
source-id: JT-SCENE1-POSITIVE-PILOT-VOLUME-NORMALIZATION
source: Joshi III `eq:multiplicative-coh-class`, the normalized square
exponents in `th:moccor-Mochizuki-form1`, and `ss:weighted-vol`.
fidelity: compares the actual dimension-normalized Haar volume of the
positive integral-log tensor hull with the normalized finite witness
product at the same root radius and actual inverse-local-degree weight.
The actual volume is exactly the ellStar^2-th power of that product, and
is strictly smaller. Original proofs; no reference implementation copied.
boundary: Scene1/Derived. The normalized product is a numerical comparison,
not the volume of a constructed different-untilt theta locus. The strict
inequality excludes only identifying these two same-completion quantities
without the square-length rescaling. No BK or paper-volume identity.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPositivePilotVolumeNormalization

open JoshiTeich.Prologue
open scoped BigOperators Valued
universe u
noncomputable section
private theorem positiveDegreeVolume
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] (P : LocalCompletion.Packet K p ι)
    (U : Set P.Tensor) (hpos : 0 < P.normalizationHaar U)
    (hfin : P.normalizationHaar U < ⊤) :
    0 < P.normalizationDegreeVolume U :=
  Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos.ne' hfin.ne) _

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

abbrev length := ThetaWitnessProduct.ellStar D
abbrev radius := ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖

def weight : ℝ := 1 / (Arithmetic.localDeg s.1 : ℝ)

def normalizedProduct : ℝ :=
  ThetaWitnessProduct.product (radius D s) (length D) (fun _ => weight D s)

local instance sourcePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

def volume : ℝ := (InitialThetaPositivePilotIntegralTensor.packet D s).normalizationDegreeVolume
  (InitialThetaPositivePilotIntegralTensor.region D s)

theorem radius_pos_lt_one : 0 < radius D s ∧ radius D s < 1 :=
  ⟨norm_pos_iff.mpr (IutInitialThetaQRootFamily.qrootAt_ne_zero D s.1),
    IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset D s.1 s.2⟩

theorem weight_mem_unitInterval : 0 < weight D s ∧ weight D s ≤ 1 := by
  have hd : (0 : ℝ) < Arithmetic.localDeg s.1 := by exact_mod_cast Arithmetic.localDeg_pos s.1
  have hd1 : (1 : ℝ) ≤ Arithmetic.localDeg s.1 := by
    exact_mod_cast Arithmetic.localDeg_pos s.1
  exact ⟨one_div_pos.mpr hd, (div_le_one hd).mpr hd1⟩

theorem normalizedProduct_bounds :
    0 < normalizedProduct D s ∧
      radius D s ^ length D ≤ normalizedProduct D s ∧ normalizedProduct D s ≤ 1 :=
  ThetaWitnessProduct.product_bounds (radius_pos_lt_one D s).1
    (radius_pos_lt_one D s).2.le _ _
    (fun _ => ⟨(weight_mem_unitInterval D s).1.le, (weight_mem_unitInterval D s).2⟩)

theorem volume_pos : 0 < volume D s :=
  positiveDegreeVolume (InitialThetaPositivePilotIntegralTensor.packet D s)
    (InitialThetaPositivePilotIntegralTensor.region D s)
    (InitialThetaPositivePilotIntegralTensor.region_haar_pos_lt_top D s).1
    (InitialThetaPositivePilotIntegralTensor.region_haar_pos_lt_top D s).2

theorem log_volume_eq_actual_logVolume :
    Real.log (volume D s) =
      (InitialThetaPositivePilotIntegralTensor.packet D s).normalizationLogVolume
        (InitialThetaPositivePilotIntegralTensor.region D s) := by
  have hpos := ENNReal.toReal_pos
    (InitialThetaPositivePilotIntegralTensor.region_haar_pos_lt_top D s).1.ne'
    (InitialThetaPositivePilotIntegralTensor.region_haar_pos_lt_top D s).2.ne
  rw [volume, LocalCompletion.Packet.normalizationDegreeVolume, Real.log_rpow hpos,
    LocalCompletion.Packet.normalizationLogVolume]
  ring

theorem log_normalizedProduct_eq_sum :
    Real.log (normalizedProduct D s) =
      ∑ j : Fin (length D), (weight D s * ThetaWitnessProduct.scale (length D) j) *
        Real.log (radius D s) := by
  have h := ThetaWitnessProduct.negLog_product_eq (radius_pos_lt_one D s).1
    (length D) (fun _ => weight D s)
  change -Real.log (normalizedProduct D s) = _ at h
  simp only [mul_neg, Finset.sum_neg_distrib] at h
  exact neg_injective h

theorem log_volume_eq_square_length_mul_log_product :
    Real.log (volume D s) = (length D : ℝ) ^ 2 * Real.log (normalizedProduct D s) := by
  rw [log_volume_eq_actual_logVolume,
    InitialThetaPositivePilotIntegralTensor.region_logVolume_eq_square_sum,
    log_normalizedProduct_eq_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hn : (length D : ℝ) ≠ 0 := by
    exact_mod_cast (ThetaWitnessProduct.ellStar_pos D).ne'
  simp only [weight, ThetaWitnessProduct.scale, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  field_simp [hn]

theorem volume_eq_normalizedProduct_pow :
    volume D s = normalizedProduct D s ^ (length D ^ 2) := by
  apply Real.log_injOn_pos (volume_pos D s)
    (pow_pos (normalizedProduct_bounds D s).1 _)
  rw [log_volume_eq_square_length_mul_log_product, Real.log_pow, Nat.cast_pow]

theorem normalizedProduct_lt_one : normalizedProduct D s < 1 := by
  have hv : Real.log (volume D s) < 0 := by
    rw [log_volume_eq_actual_logVolume]
    exact InitialThetaPositivePilotIntegralTensor.region_logVolume_neg D s
  have hsq : 0 < (length D : ℝ) ^ 2 := by
    have hn : (0 : ℝ) < length D := by exact_mod_cast ThetaWitnessProduct.ellStar_pos D
    positivity
  have hp : Real.log (normalizedProduct D s) < 0 := by
    rw [log_volume_eq_square_length_mul_log_product] at hv
    exact neg_of_mul_neg_right hv hsq.le
  exact (Real.log_neg_iff (normalizedProduct_bounds D s).1).mp hp

theorem volume_lt_normalizedProduct : volume D s < normalizedProduct D s := by
  have hn : 2 ≤ length D := by
    have h := D.prime.five_le
    change 2 ≤ (D.prime.ℓ - 1) / 2
    omega
  have hs : (1 : ℝ) < (length D : ℝ) ^ 2 := by
    have hn' : (2 : ℝ) ≤ length D := by exact_mod_cast hn
    nlinarith
  apply (Real.strictMonoOn_log.lt_iff_lt (volume_pos D s)
    (normalizedProduct_bounds D s).1).mp
  rw [log_volume_eq_square_length_mul_log_product]
  have hp : Real.log (normalizedProduct D s) < 0 :=
    Real.log_neg (normalizedProduct_bounds D s).1 (normalizedProduct_lt_one D s)
  nlinarith

end
end JoshiTeich.Act1Scene1.InitialThetaPositivePilotVolumeNormalization
