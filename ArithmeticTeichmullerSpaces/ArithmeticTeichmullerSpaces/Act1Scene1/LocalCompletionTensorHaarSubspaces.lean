/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/Hull.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt proper-subspace nullity and nonzero residue witnesses to
actual Packet topology and its constructed normalization Haar measure.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHaar

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-HAAR-RESIDUE-WITNESSES
fidelity: proves actual proper Q_p subspaces have zero normalization Haar
measure, so positive-measure regions have a nonzero point in every residue
coordinate. No nonzero-coordinate certificate is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
open scoped Pointwise Function
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance subspaceFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance subspaceFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance subspaceTensorFinite : Module.Finite ℚ_[p] P.Tensor :=
  Module.Finite.of_basis P.tensorBasis

theorem normalizationHaar_submodule_eq_zero (S : Submodule ℚ_[p] P.Tensor) (hS : S ≠ ⊤) :
    P.normalizationHaar (S : Set P.Tensor) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hS
  set u : ℕ → P.Tensor := fun n => ((n : ℕ) : ℚ_[p]) • x with hu_def
  have hu : Bornology.IsBounded (Set.range u) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨‖x‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [hu_def, norm_smul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact_mod_cast Padic.norm_int_le_one (n : ℤ)
  have hmeas : MeasurableSet (S : Set P.Tensor) :=
    (Submodule.closed_of_finiteDimensional S).measurableSet
  have hdisj : Pairwise (Disjoint on fun n => {u n} + (S : Set P.Tensor)) := by
    intro n k hnk
    simp only [Function.onFun, Set.singleton_add, Set.image_add_left, Set.disjoint_left,
      Set.mem_preimage, SetLike.mem_coe]
    intro y hyn hyk
    have hmem : ((k : ℚ_[p]) - n) • x ∈ S := by
      have := S.sub_mem hyn hyk
      rw [neg_add_eq_sub, neg_add_eq_sub, sub_sub_sub_cancel_left] at this
      change (k : ℚ_[p]) • x - (n : ℚ_[p]) • x ∈ S at this
      rwa [← sub_smul] at this
    have hne : ((k : ℚ_[p]) - n) ≠ 0 := sub_ne_zero.mpr (Nat.cast_injective.ne hnk.symm)
    apply hx
    have := S.smul_mem ((k : ℚ_[p]) - n)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have key : ∀ R : ℝ, P.normalizationHaar
      ((S : Set P.Tensor) ∩ Metric.closedBall 0 R) = 0 := by
    intro R
    set s := (S : Set P.Tensor) ∩ Metric.closedBall 0 R with hs
    have hsb : Bornology.IsBounded s := Metric.isBounded_closedBall.subset Set.inter_subset_right
    have hsm : MeasurableSet s := hmeas.inter Metric.isClosed_closedBall.measurableSet
    have hdisj' : Pairwise (Disjoint on fun n => {u n} + s) :=
      pairwise_disjoint_mono hdisj fun n => Set.add_subset_add subset_rfl Set.inter_subset_left
    by_contra h
    apply lt_irrefl (⊤ : ENNReal)
    calc (⊤ : ENNReal) = ∑' _ : ℕ, P.normalizationHaar s :=
          (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
      _ = ∑' n : ℕ, P.normalizationHaar ({u n} + s) := by
          congr 1
          ext1 n
          simp only [Set.image_add_left, measure_preimage_add, Set.singleton_add]
      _ = P.normalizationHaar (⋃ n, {u n} + s) :=
          Eq.symm <| measure_iUnion hdisj' fun n => by
            have hm : Measurable fun y : P.Tensor => -u n + y :=
              (continuous_const.add continuous_id).measurable
            simpa only [Set.image_add_left, Set.singleton_add] using hm hsm
      _ = P.normalizationHaar (Set.range u + s) := by
          rw [← Set.iUnion_add, Set.iUnion_singleton_eq_range]
      _ < ⊤ := (hu.add hsb).measure_lt_top
  rw [← nonpos_iff_eq_zero]
  calc P.normalizationHaar (S : Set P.Tensor)
      ≤ ∑' n : ℕ, P.normalizationHaar
          ((S : Set P.Tensor) ∩ Metric.closedBall 0 n) := by
        conv_lhs => rw [← Metric.iUnion_inter_closedBall_nat (S : Set P.Tensor) 0]
        exact measure_iUnion_le _
    _ = 0 := by simp only [key, tsum_zero]

/-- A region of positive Haar measure has a point with nonzero residue at every maximal
ideal. -/
lemma exists_residue_ne_zero_of_haar_pos {U : Set P.Tensor}
    (hU : 0 < P.normalizationHaar U) (m : MaximalSpectrum P.Tensor) :
    ∃ x ∈ U, Ideal.Quotient.mk m.asIdeal x ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : U ⊆ (m.asIdeal.restrictScalars ℚ_[p] : Set P.Tensor) := by
    intro x hx
    have := h x hx
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this
  have hne : m.asIdeal.restrictScalars ℚ_[p] ≠ ⊤ := by
    intro htop
    have h1 : (1 : P.Tensor) ∈ m.asIdeal := Submodule.eq_top_iff'.mp htop 1
    exact m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact absurd hU (not_lt.mpr ((measure_mono hsub).trans
    (P.normalizationHaar_submodule_eq_zero _ hne).le))

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
