import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorLogGenerators
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadCollatedNormalizationVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFixedModuliNormalizationVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-LOG-GENERATED-HULL
source: actual canonical q-root ordinary logs, small-ball log surjectivity,
and Joshi III multiplicative log-shell/hull volume picture.
fidelity: constructs actual log-image collation with derived generator
coverage and normalization containment. Its global hull Haar volume is
exactly the canonical normalized VBad root product to the tuple length.
No collation or geometric certificate is an input. The construction is in
the original completions; paper theta/Bloch-Kato/different-untilt and weighted
volume identities are not asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadThetaLogCollation
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
local instance logCollationPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩

abbrev packet (v : iutInitialThetaVBadModuliFinset D) :=
  VBadThetaCollatedHull.packet D n σ hσ v

local instance logCollationIntegralModule (v : iutInitialThetaVBadModuliFinset D) :
    Module ℤ_[Arithmetic.residueChar v.1] (packet D n σ hσ v).Tensor :=
  Module.compHom (packet D n σ hσ v).Tensor
    (algebraMap ℤ_[Arithmetic.residueChar v.1] ℚ_[Arithmetic.residueChar v.1])

def collation (v : iutInitialThetaVBadModuliFinset D) (_ : Unit) :
    Set (packet D n σ hσ v).Tensor :=
  (packet D n σ hσ v).logScalarGenerators (fun i => iutInitialThetaFullQRootLogValue D (σ v i))

def volume : ℝ := VBadThetaCollatedHull.volume D n σ hσ (collation D n σ hσ)

theorem generator_coverage (v : iutInitialThetaVBadModuliFinset D) :
    (packet D n σ hσ v).scalarGenerators
      (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, collation D n σ hσ v k := by
  simp only [collation, Set.iUnion_const]
  rw [(packet D n σ hσ v).logScalarGenerators_eq_scalarGenerators]

theorem collation_subset_normalization (v : iutInitialThetaVBadModuliFinset D) (k : Unit) :
    collation D n σ hσ v k ⊆ (packet D n σ hσ v).normalization := by
  apply Set.Subset.trans _ (packet D n σ hσ v).unitLattice_le_normalization
  apply (packet D n σ hσ v).logScalarGenerators_subset_unitLattice
  intro i
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact (iutInitialThetaFullQRoot_norm_lt_one D _).le

theorem region_eq_scalarNormalization (v : iutInitialThetaVBadModuliFinset D) :
    (VBadThetaCollatedHull.region D n σ hσ (collation D n σ hσ) v :
      Set (packet D n σ hσ v).Tensor) =
      (FixedModuliThetaNormalization.region D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v) :
        Set (packet D n σ hσ v).Tensor) := by
  change ((packet D n σ hσ v).normalizationHull
    (⋃ k, collation D n σ hσ v k) : Set (packet D n σ hσ v).Tensor) = _
  simp only [collation, Set.iUnion_const]
  unfold FixedModuliThetaNormalization.region
  apply (packet D n σ hσ v).normalizationHull_logScalarGenerators _
    (fun i => norm_ne_zero_iff.mp (by
      rw [iutInitialThetaFullQRootLogValue_norm_eq]
      exact norm_ne_zero_iff.mpr
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)))

theorem volume_eq_normalizedRootProduct_pow :
    volume D n σ hσ = iutInitialThetaNormalizedVBadRelativeQRootProduct D ^ n := by
  have hlocal (v : iutInitialThetaVBadModuliFinset D) :
      (packet D n σ hσ v).normalizationDegreeVolume
          (VBadThetaCollatedHull.region D n σ hσ (collation D n σ hσ) v) ^ Arithmetic.localDeg v.1 =
        iutInitialThetaRelativeQRootFactor D (iutInitialThetaVBadModuliAt D v) ^ n := by
    rw [region_eq_scalarNormalization D n σ hσ v]
    change FixedModuliThetaNormalization.volume D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v) = _
    simpa only [Fintype.card_fin] using FixedModuliThetaNormalization.volume_eq_relativeFactor_pow
      D (iutInitialThetaVBadModuliAt D v) (σ v) (hσ v)
  unfold volume VBadThetaCollatedHull.volume
  simp only [hlocal]
  rw [Finset.prod_pow, ← iutInitialThetaVBadRelativeQRootProduct,
    ← Real.rpow_pow_comm (iutInitialThetaVBadRelativeQRootProduct_pos D).le]
  rfl

theorem volume_pos : 0 < volume D n σ hσ :=
  VBadThetaCollatedHull.volume_pos D n σ hσ (collation D n σ hσ)
    (generator_coverage D n σ hσ) (collation_subset_normalization D n σ hσ)

theorem volume_le_one : volume D n σ hσ ≤ 1 :=
  VBadThetaCollatedHull.volume_le_one D n σ hσ (collation D n σ hσ)
    (collation_subset_normalization D n σ hσ)

theorem negLog_volume_eq_mul_referenceAbsLogQ :
    -Real.log (volume D n σ hσ) = (n : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [volume_eq_normalizedRootProduct_pow, Real.log_pow,
    ← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D]
  rw [mul_neg]

theorem absLog_volume_eq_mul_referenceAbsLogQ :
    |Real.log (volume D n σ hσ)| = (n : ℝ) *
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [abs_of_nonpos (Real.log_nonpos (volume_pos D n σ hσ).le (volume_le_one D n σ hσ))]
  exact negLog_volume_eq_mul_referenceAbsLogQ D n σ hσ

theorem negAverageAbsLog_volume_eq_referenceLhs (hn : 0 < n) :
    -(1 / (n : ℝ)) * |Real.log (volume D n σ hσ)| =
      -JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [absLog_volume_eq_mul_referenceAbsLogQ, neg_mul, ← mul_assoc,
    one_div_mul_cancel hn'.ne', one_mul]

end
end JoshiTeich.Act1Scene1.VBadThetaLogCollation
