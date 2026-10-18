import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensorLogShell
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
source-id: JT-SCENE1-LOCAL-ARCHIMEDEAN-TENSOR-HAAR
source: IUT IV Proposition 1.5; reference `LocalConstruct/ArchLogShell.lean`
uses pi^|I| B_I and positive finite Haar admissibility. Mathlib
`Measure.addHaarMeasure` and `addHaar_smul_of_nonneg` construct the measure.
fidelity: normalizes the actual archimedean tensor Haar measure on B_I,
computes the exact pi^|I| shell measure and dimension-normalized real
log-volume, and proves positive finite measure of its full factor orbit.
No paper theta-value or adelic volume identity is asserted.
Original proofs; no reference code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalArchimedean

open NumberField MeasureTheory TopologicalSpace
open scoped BigOperators Pointwise

universe u
noncomputable section
variable {K : Type u} [Field K] {ι : Type} [Fintype ι] (c : ι → InfinitePlace K)

instance tensorSecondCountable : SecondCountableTopology (Tensor c) :=
  (tensorBasis c).equivFunL.toHomeomorph.isInducing.secondCountableTopology
instance tensorMeasurableSpace : MeasurableSpace (Tensor c) := borel _
instance tensorBorelSpace : BorelSpace (Tensor c) := ⟨rfl⟩

def integralPositiveCompact : PositiveCompacts (Tensor c) where
  carrier := archIntegral c
  isCompact' := isCompact_archIntegral c
  interior_nonempty' := by
    obtain ⟨r, hr, hball⟩ := exists_ball_subset_archIntegral c
    exact ⟨0, mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) hball)⟩

def normalizedHaar : Measure (Tensor c) := Measure.addHaarMeasure (integralPositiveCompact c)

instance normalizedHaar_isAddHaarMeasure : (normalizedHaar c).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure (integralPositiveCompact c)).IsAddHaarMeasure
instance normalizedHaar_regular : (normalizedHaar c).Regular :=
  inferInstanceAs (Measure.addHaarMeasure (integralPositiveCompact c)).Regular

theorem normalizedHaar_archIntegral : normalizedHaar c (archIntegral c) = 1 :=
  Measure.addHaarMeasure_self

theorem normalizedHaar_archLogShell : normalizedHaar c (archLogShell c) =
    ENNReal.ofReal ((Real.pi ^ Fintype.card ι) ^ Module.finrank ℝ (Tensor c)) := by
  rw [archLogShell, Measure.addHaar_smul_of_nonneg (normalizedHaar c)
    (pow_nonneg Real.pi_pos.le _), normalizedHaar_archIntegral, mul_one]

theorem archLogShell_haar_pos_lt_top :
    0 < normalizedHaar c (archLogShell c) ∧ normalizedHaar c (archLogShell c) < ⊤ := by
  rw [normalizedHaar_archLogShell]
  exact ⟨ENNReal.ofReal_pos.mpr (pow_pos (pow_pos Real.pi_pos _) _), ENNReal.ofReal_lt_top⟩

theorem factorOrbit_archLogShell_haar_pos_lt_top :
    0 < normalizedHaar c (factorOrbit c (archLogShell c)) ∧
      normalizedHaar c (factorOrbit c (archLogShell c)) < ⊤ := by
  rw [factorOrbit_archLogShell]
  exact archLogShell_haar_pos_lt_top c

theorem tensor_finrank_pos : 0 < Module.finrank ℝ (Tensor c) := by
  rw [Module.finrank_eq_card_basis (tensorBasis c)]
  have : Nonempty (BasisIndex c) :=
    ⟨fun j => ⟨0, Module.finrank_pos (R := ℝ) (M := Factor (c j))⟩⟩
  exact Fintype.card_pos

def normalizationLogVolume (S : Set (Tensor c)) : ℝ :=
  Real.log (normalizedHaar c S).toReal / (Module.finrank ℝ (Tensor c) : ℝ)

theorem normalizationLogVolume_archIntegral :
    normalizationLogVolume c (archIntegral c) = 0 := by
  simp only [normalizationLogVolume, normalizedHaar_archIntegral, ENNReal.toReal_one,
    Real.log_one, zero_div]

theorem normalizationLogVolume_archLogShell :
    normalizationLogVolume c (archLogShell c) = (Fintype.card ι : ℝ) * Real.log Real.pi := by
  unfold normalizationLogVolume
  rw [normalizedHaar_archLogShell, ENNReal.toReal_ofReal (by positivity),
    Real.log_pow, Real.log_pow]
  have hd : (Module.finrank ℝ (Tensor c) : ℝ) ≠ 0 := by
    exact_mod_cast (tensor_finrank_pos c).ne'
  field_simp

theorem normalizationLogVolume_archLogShell_nonneg :
    0 ≤ normalizationLogVolume c (archLogShell c) := by
  rw [normalizationLogVolume_archLogShell]
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [Real.two_le_pi]))

end
end JoshiTeich.Act1Scene1.LocalArchimedean
