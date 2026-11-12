import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRepeatedHaarProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorVolumeMonotonicity

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-REGION-VOLUME-BOUND
source: Joshi III th:moccor-Mochizuki-form2 (3624--3631) and cor:cor312
(3634--3650), set containment followed by Haar monotonicity and log signs.
fidelity: defines a volume from actual region Haar measures and derives a
relative-degree VBad q-pilot bound from explicit repeated-log-lattice
containment. Upper containment in the actual tensor unit lattice supplies
the sign condition. No theta region, untilt/Bloch-Kato witness, paper
maximal order or paper volume normalization is constructed here.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue MeasureTheory
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (ρ : iutInitialThetaVBadModuliFinset D →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (n : ℕ)
local instance sourcePrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar (ρ v).1).Prime :=
  ⟨Arithmetic.residueChar_prime (ρ v).1⟩
local instance integralModule (v : iutInitialThetaVBadModuliFinset D) :
    Module ℤ_[Arithmetic.residueChar (ρ v).1] (RepeatedThetaRoot.packet D (ρ v) n).Tensor :=
  Module.compHom (RepeatedThetaRoot.packet D (ρ v) n).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar (ρ v).1] ℚ_[Arithmetic.residueChar (ρ v).1])
variable (H : ∀ v : iutInitialThetaVBadModuliFinset D,
  Set (RepeatedThetaRoot.packet D (ρ v) n).Tensor)

def iutInitialThetaVBadRegionVolume : ℝ :=
  (∏ v : iutInitialThetaVBadModuliFinset D,
    (RepeatedThetaRoot.packet D (ρ v) n).degreeVolume (H v) ^ Arithmetic.localDeg v.1) ^
      (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

theorem iutInitialThetaVBadRepeatedHaarProduct_le_regionVolume
    (hcontains : ∀ v, (RepeatedThetaRoot.region D (ρ v) n :
      Set (RepeatedThetaRoot.packet D (ρ v) n).Tensor) ⊆ H v)
    (hfinite : ∀ v, (RepeatedThetaRoot.packet D (ρ v) n).normalizedHaar (H v) ≠ ⊤) :
    iutInitialThetaVBadRepeatedHaarProduct D ρ n ≤ iutInitialThetaVBadRegionVolume D ρ n H := by
  unfold iutInitialThetaVBadRepeatedHaarProduct iutInitialThetaVBadRegionVolume
  apply Real.rpow_le_rpow
    (Finset.prod_nonneg fun v _ => (RepeatedThetaRoot.moduliVolume_pos D (ρ v) n v.1).le)
    _ (by positivity)
  apply Finset.prod_le_prod
    (fun v _ => (RepeatedThetaRoot.moduliVolume_pos D (ρ v) n v.1).le)
  intro v _
  exact pow_le_pow_left₀
    ((RepeatedThetaRoot.packet D (ρ v) n).degreeVolume_nonneg (RepeatedThetaRoot.region D (ρ v) n))
    ((RepeatedThetaRoot.packet D (ρ v) n).degreeVolume_mono (hcontains v) (hfinite v)) _

theorem iutInitialThetaVBadRegionVolume_le_one
    (hunit : ∀ v, H v ⊆ (RepeatedThetaRoot.packet D (ρ v) n).unitLattice) :
    iutInitialThetaVBadRegionVolume D ρ n H ≤ 1 := by
  unfold iutInitialThetaVBadRegionVolume
  apply Real.rpow_le_one
    (Finset.prod_nonneg fun v _ => pow_nonneg
      ((RepeatedThetaRoot.packet D (ρ v) n).degreeVolume_nonneg (H v)) _)
    _ (by positivity)
  apply Finset.prod_le_one
    (fun v _ => pow_nonneg
      ((RepeatedThetaRoot.packet D (ρ v) n).degreeVolume_nonneg (H v)) _)
  intro v _
  exact pow_le_one₀ ((RepeatedThetaRoot.packet D (ρ v) n).degreeVolume_nonneg (H v))
    ((RepeatedThetaRoot.packet D (ρ v) n).degreeVolume_le_one_of_subset_unitLattice _ (hunit v))

private theorem repeatedProduct_pos : 0 < iutInitialThetaVBadRepeatedHaarProduct D ρ n := by
  exact Real.rpow_pos_of_pos
    (Finset.prod_pos fun v _ => RepeatedThetaRoot.moduliVolume_pos D (ρ v) n v.1) _

theorem iutInitialThetaVBadRegionVolume_pos
    (hcontains : ∀ v, (RepeatedThetaRoot.region D (ρ v) n :
      Set (RepeatedThetaRoot.packet D (ρ v) n).Tensor) ⊆ H v)
    (hfinite : ∀ v, (RepeatedThetaRoot.packet D (ρ v) n).normalizedHaar (H v) ≠ ⊤) :
    0 < iutInitialThetaVBadRegionVolume D ρ n H := by
  exact (repeatedProduct_pos D ρ n).trans_le
    (iutInitialThetaVBadRepeatedHaarProduct_le_regionVolume D ρ n H hcontains hfinite)

variable (hρ : ∀ v, Ideal.LiesOver (ρ v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)

include hρ in
theorem iutInitialThetaVBadRegionVolume_absLog_le
    (hcontains : ∀ v, (RepeatedThetaRoot.region D (ρ v) n :
      Set (RepeatedThetaRoot.packet D (ρ v) n).Tensor) ⊆ H v)
    (hunit : ∀ v, H v ⊆ (RepeatedThetaRoot.packet D (ρ v) n).unitLattice) :
    |Real.log (iutInitialThetaVBadRegionVolume D ρ n H)| ≤
      (n : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hfinite : ∀ v, (RepeatedThetaRoot.packet D (ρ v) n).normalizedHaar (H v) ≠ ⊤ := by
    intro v
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (measure_mono (hunit v)).trans_eq
      (RepeatedThetaRoot.packet D (ρ v) n).normalizedHaar_unitLattice
  have hpos := iutInitialThetaVBadRegionVolume_pos D ρ n H hcontains hfinite
  rw [abs_of_nonpos (Real.log_nonpos hpos.le
    (iutInitialThetaVBadRegionVolume_le_one D ρ n H hunit)),
    ← iutInitialThetaVBadRepeatedHaarProduct_negLog_eq_mul_referenceAbsLogQ D ρ n hρ]
  exact neg_le_neg (Real.log_le_log (repeatedProduct_pos D ρ n)
    (iutInitialThetaVBadRepeatedHaarProduct_le_regionVolume D ρ n H hcontains hfinite))

include hρ in
theorem iutInitialThetaVBadRegionVolume_negAverageAbsLog_ge_referenceLhs
    (hn : 0 < n)
    (hcontains : ∀ v, (RepeatedThetaRoot.region D (ρ v) n :
      Set (RepeatedThetaRoot.packet D (ρ v) n).Tensor) ⊆ H v)
    (hunit : ∀ v, H v ⊆ (RepeatedThetaRoot.packet D (ρ v) n).unitLattice) :
    -(1 / (n : ℝ)) * |Real.log (iutInitialThetaVBadRegionVolume D ρ n H)| ≥
      -JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left
    (iutInitialThetaVBadRegionVolume_absLog_le D ρ n H hρ hcontains hunit)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  have hcancel : (1 / (n : ℝ)) * ((n : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D)) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
    rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]
  rw [hcancel] at h
  simpa only [neg_mul] using neg_le_neg h

end
end JoshiTeich.Act1Scene1
