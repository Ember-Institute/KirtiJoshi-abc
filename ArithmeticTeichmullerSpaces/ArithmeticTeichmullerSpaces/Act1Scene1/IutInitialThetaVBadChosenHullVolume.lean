import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliTensorVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRelativeQRootProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHullNormalizationBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorVolumeMonotonicity

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-CHOSEN-HULL-VOLUME
source: actual fixed-moduli hull Haar lower bound and exact actual VBad
q-pilot product; Joshi III multiplicative adelic volume (3624--3631).
fidelity: defines global volume directly from actual local chosen hull Haar,
derives the normalized VBad root product lower bound and negative-average
log bound. Actual ordinary log lattice containment and normalization upper
containment remain explicit geometric inputs. No theta/untilt/Bloch-Kato
source or paper C_p/weighted-volume identification is constructed here.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadThetaHull
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
local instance globalHullPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

abbrev packet (v : iutInitialThetaVBadModuliFinset D) :=
  FixedModuliThetaTensor.packet D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v)

local instance globalHullIntegralModule (v : iutInitialThetaVBadModuliFinset D) :
    Module ℤ_[Arithmetic.residueChar v.1] (packet D n σ hσ v).Tensor :=
  Module.compHom (packet D n σ hσ v).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])
variable (U : ∀ v : iutInitialThetaVBadModuliFinset D, Set (packet D n σ hσ v).Tensor)
variable (hU : ∀ v, Bornology.IsBounded (U v))
variable (hpos : ∀ v, 0 < (packet D n σ hσ v).normalizationHaar (U v))

def volume : ℝ :=
  (∏ v : iutInitialThetaVBadModuliFinset D,
    (packet D n σ hσ v).normalizationDegreeVolume
      ((packet D n σ hσ v).leastHull (U v) (hU v) (hpos v)) ^ Arithmetic.localDeg v.1) ^
    (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

theorem volume_pos : 0 < volume D n σ hσ U hU hpos := by
  unfold volume
  apply Real.rpow_pos_of_pos
  apply Finset.prod_pos
  intro v _
  exact pow_pos ((packet D n σ hσ v).leastHull_normalizationDegreeVolume_pos
    (U v) (hU v) (hpos v)) _

theorem normalizedRootProduct_pow_le_volume
    (hregion : ∀ v, (FixedModuliThetaTensor.region D (iutInitialThetaVBadModuliAt D v)
      (σ v) (hσ v) : Set (packet D n σ hσ v).Tensor) ⊆ U v) :
    iutInitialThetaNormalizedVBadRelativeQRootProduct D ^ n ≤ volume D n σ hσ U hU hpos := by
  have hlocal (v : iutInitialThetaVBadModuliFinset D) :=
    (packet D n σ hσ v).degreeVolume_scalarLattice_le_leastHullVolume
      (fun i => iutInitialThetaFullQRootLogValue D (σ v i))
      (fun i => norm_ne_zero_iff.mp (by
        rw [iutInitialThetaFullQRootLogValue_norm_eq]
        exact norm_ne_zero_iff.mpr
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)))
      (U v) (hU v) (hpos v) (hregion v)
  have hlocalPow (v : iutInitialThetaVBadModuliFinset D) :=
    pow_le_pow_left₀
      ((packet D n σ hσ v).degreeVolume_nonneg
        (FixedModuliThetaTensor.region D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v)))
      (hlocal v) (Arithmetic.localDeg v.1)
  have hfactor (v : iutInitialThetaVBadModuliFinset D) :
      iutInitialThetaRelativeQRootFactor D (iutInitialThetaVBadModuliAt D v) ^ n ≤
        (packet D n σ hσ v).normalizationDegreeVolume
          ((packet D n σ hσ v).leastHull (U v) (hU v) (hpos v)) ^
            Arithmetic.localDeg v.1 := by
    have h := hlocalPow v
    change FixedModuliThetaTensor.volume D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v) ≤
      (packet D n σ hσ v).normalizationDegreeVolume
        ((packet D n σ hσ v).leastHull (U v) (hU v) (hpos v)) ^ Arithmetic.localDeg v.1 at h
    simpa only [FixedModuliThetaTensor.volume_eq_relativeFactor_pow, Fintype.card_fin] using h
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
    (fun v _ => hfactor v)

theorem volume_le_one (hunit : ∀ v, U v ⊆ (packet D n σ hσ v).normalization) :
    volume D n σ hσ U hU hpos ≤ 1 := by
  unfold volume
  have hlocal (v : iutInitialThetaVBadModuliFinset D) :
      (packet D n σ hσ v).normalizationDegreeVolume
        ((packet D n σ hσ v).leastHull (U v) (hU v) (hpos v)) ^ Arithmetic.localDeg v.1 ≤ 1 := by
    apply pow_le_one₀
      ((packet D n σ hσ v).leastHull_normalizationDegreeVolume_pos (U v) (hU v) (hpos v)).le
    exact (packet D n σ hσ v).normalizationDegreeVolume_le_one _
      ((packet D n σ hσ v).leastHull_subset_normalization (U v) (hU v) (hpos v) (hunit v))
  apply Real.rpow_le_one
  · exact Finset.prod_nonneg fun v _ => pow_nonneg
      ((packet D n σ hσ v).leastHull_normalizationDegreeVolume_pos (U v) (hU v) (hpos v)).le _
  · exact Finset.prod_le_one₀
      (fun v _ => pow_nonneg
        ((packet D n σ hσ v).leastHull_normalizationDegreeVolume_pos (U v) (hU v) (hpos v)).le _)
      (fun v _ => hlocal v)
  · positivity

theorem absLog_volume_le_mul_referenceAbsLogQ
    (hregion : ∀ v, (FixedModuliThetaTensor.region D (iutInitialThetaVBadModuliAt D v)
      (σ v) (hσ v) : Set (packet D n σ hσ v).Tensor) ⊆ U v)
    (hunit : ∀ v, U v ⊆ (packet D n σ hσ v).normalization) :
    |Real.log (volume D n σ hσ U hU hpos)| ≤ (n : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hlog := Real.log_le_log
    (pow_pos (iutInitialThetaNormalizedVBadRelativeQRootProduct_pos D) n)
    (normalizedRootProduct_pow_le_volume D n σ hσ U hU hpos hregion)
  rw [Real.log_pow] at hlog
  rw [abs_of_nonpos (Real.log_nonpos (volume_pos D n σ hσ U hU hpos).le
    (volume_le_one D n σ hσ U hU hpos hunit)),
    ← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D]
  simpa only [mul_neg] using neg_le_neg hlog

theorem negAverageAbsLog_volume_ge_referenceLhs (hn : 0 < n)
    (hregion : ∀ v, (FixedModuliThetaTensor.region D (iutInitialThetaVBadModuliAt D v)
      (σ v) (hσ v) : Set (packet D n σ hσ v).Tensor) ⊆ U v)
    (hunit : ∀ v, U v ⊆ (packet D n σ hσ v).normalization) :
    -(1 / (n : ℝ)) * |Real.log (volume D n σ hσ U hU hpos)| ≥
      -JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left
    (absLog_volume_le_mul_referenceAbsLogQ D n σ hσ U hU hpos hregion hunit)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul] at h
  simpa only [neg_mul] using neg_le_neg h

end
end JoshiTeich.Act1Scene1.VBadThetaHull
