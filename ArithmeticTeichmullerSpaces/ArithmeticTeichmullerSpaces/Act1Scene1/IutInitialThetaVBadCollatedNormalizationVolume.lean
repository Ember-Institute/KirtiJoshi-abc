import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCollatedPrincipalHullLaws
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRelativeQRootProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-COLLATED-NORMALIZATION-VOLUME
source: Joshi III multiplicative adelic hull volume (3624--3631) and actual
VBad relative q-root accounting.
fidelity: defines global volume from actual local collated principal hull
Haar measures. Original collation generator coverage and normalization
containment derive positivity, finiteness, the relative root product lower
bound and negative-average log bound. No boundedness, positive-measure or
free volume certificate is an input. Paper norm, carrier and theta/Bloch-Kato
identities remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadThetaCollatedHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
local instance globalCollationPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

abbrev packet (v : iutInitialThetaVBadModuliFinset D) :=
  FixedModuliThetaTensor.packet D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v)

local instance globalCollationIntegralModule (v : iutInitialThetaVBadModuliFinset D) :
    Module ℤ_[Arithmetic.residueChar v.1] (packet D n σ hσ v).Tensor :=
  Module.compHom (packet D n σ hσ v).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D, κ → Set (packet D n σ hσ v).Tensor)

abbrev region (v : iutInitialThetaVBadModuliFinset D) :=
  FixedModuliThetaCollatedHull.region D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v) (C v)

def volume : ℝ :=
  (∏ v : iutInitialThetaVBadModuliFinset D,
    (packet D n σ hσ v).normalizationDegreeVolume (region D n σ hσ C v) ^ Arithmetic.localDeg v.1) ^
    (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

variable (hgen : ∀ v, (packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (packet D n σ hσ v).normalization)

include hgen hunit in
theorem region_haar_pos_lt_top (v : iutInitialThetaVBadModuliFinset D) :
    0 < (packet D n σ hσ v).normalizationHaar (region D n σ hσ C v) ∧
      (packet D n σ hσ v).normalizationHaar (region D n σ hσ C v) < ⊤ := by
  obtain ⟨a, ha, heq, _, _⟩ := FixedModuliThetaCollatedHull.region_is_least_principal
    D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v) (C v) (hgen v) (hunit v)
  change (region D n σ hσ C v : Set (packet D n σ hσ v).Tensor) =
    (packet D n σ hσ v).principalRegion a at heq
  rw [heq]
  exact (packet D n σ hσ v).principalRegion_haar_pos_lt_top a ha

include hgen hunit in
theorem normalizedRootProduct_pow_le_volume :
    iutInitialThetaNormalizedVBadRelativeQRootProduct D ^ n ≤ volume D n σ hσ C := by
  have hlocal (v : iutInitialThetaVBadModuliFinset D) :=
    FixedModuliThetaCollatedHull.relativeFactor_pow_le_volume D (iutInitialThetaVBadModuliAt D v)
      (σ v) (hσ v) (C v) (hgen v) (hunit v)
  simp only [Fintype.card_fin] at hlocal
  rw [iutInitialThetaNormalizedVBadRelativeQRootProduct, Real.rpow_pow_comm
    (iutInitialThetaVBadRelativeQRootProduct_pos D).le,
    iutInitialThetaVBadRelativeQRootProduct, ← Finset.prod_pow, volume]
  apply Real.rpow_le_rpow
    (Finset.prod_nonneg fun v _ => pow_nonneg
      (iutInitialThetaRelativeQRootFactor_mem_Ioo D (iutInitialThetaVBadModuliAt D v)).1.le _)
    _ (by positivity)
  exact Finset.prod_le_prod₀
    (fun v _ => pow_nonneg
      (iutInitialThetaRelativeQRootFactor_mem_Ioo D (iutInitialThetaVBadModuliAt D v)).1.le _)
    (fun v _ => hlocal v)

include hgen hunit in
theorem volume_pos : 0 < volume D n σ hσ C :=
  (pow_pos (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D) n).trans_le
    (normalizedRootProduct_pow_le_volume D n σ hσ C hgen hunit)

include hunit in
theorem volume_le_one : volume D n σ hσ C ≤ 1 := by
  unfold volume
  have hnonneg (v : iutInitialThetaVBadModuliFinset D) :
      0 ≤ (packet D n σ hσ v).normalizationDegreeVolume (region D n σ hσ C v) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hlocal (v : iutInitialThetaVBadModuliFinset D) :=
    FixedModuliThetaCollatedHull.volume_le_one D (iutInitialThetaVBadModuliAt D v)
      (σ v) (hσ v) (C v) (hunit v)
  exact Real.rpow_le_one
    (Finset.prod_nonneg fun v _ => pow_nonneg (hnonneg v) _)
    (Finset.prod_le_one₀ (fun v _ => pow_nonneg (hnonneg v) _) (fun v _ => hlocal v))
    (by positivity)

include hgen hunit in
theorem absLog_volume_le_mul_referenceAbsLogQ :
    |Real.log (volume D n σ hσ C)| ≤ (n : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hlog := Real.log_le_log (pow_pos (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D) n)
    (normalizedRootProduct_pow_le_volume D n σ hσ C hgen hunit)
  rw [Real.log_pow] at hlog
  rw [abs_of_nonpos (Real.log_nonpos (volume_pos D n σ hσ C hgen hunit).le
    (volume_le_one D n σ hσ C hunit)),
    ← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D]
  simpa only [mul_neg] using neg_le_neg hlog

include hgen hunit in
theorem negAverageAbsLog_volume_ge_referenceLhs (hn : 0 < n) :
    -(1 / (n : ℝ)) * |Real.log (volume D n σ hσ C)| ≥
      -JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left
    (absLog_volume_le_mul_referenceAbsLogQ D n σ hσ C hgen hunit)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul] at h
  simpa only [neg_mul] using neg_le_neg h

end
end JoshiTeich.Act1Scene1.VBadThetaCollatedHull
