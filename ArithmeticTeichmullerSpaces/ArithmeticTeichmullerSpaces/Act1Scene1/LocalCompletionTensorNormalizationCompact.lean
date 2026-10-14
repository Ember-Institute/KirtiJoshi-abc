/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/MaximalOrder.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: b76207ab8955e68a7408d5d2a770b75a30c3bebf
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt residue integral-closure finiteness and bounded-span proofs
to actual completion tensors and the proved normalization/residue decomposition.
No reference junk quotient, hull or volume contract is copied.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueDecomposition
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-COMPACT
source: reviewed reference MaximalOrder finite integral closure and compactness;
actual reduced Artinian tensor and Mathlib finite separable integral closure.
fidelity: proves actual Z_p normalization finite, bounded and compact in the
existing basis topology. No paper norm, hull or theta-volume identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open scoped TensorProduct
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance compactFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance compactFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)

instance normalizationQuotientTower (I : Ideal P.Tensor) :
    IsScalarTower ℤ_[p] ℚ_[p] (P.Tensor ⧸ I) :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := ℚ_[p]) (A := P.Tensor ⧸ I) fun r => rfl

theorem residueNormalization_module_finite (I : MaximalSpectrum P.Tensor) :
    Module.Finite ℤ_[p] (integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal)) := by
  haveI := I.isMaximal
  letI : Field (P.Tensor ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  haveI : Module.Finite ℚ_[p] (P.Tensor ⧸ I.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] I.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : IsNoetherian ℤ_[p] (integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal)) :=
    IsIntegralClosure.isNoetherian ℤ_[p] ℚ_[p] (P.Tensor ⧸ I.asIdeal) _
  infer_instance

theorem normalization_module_finite : Module.Finite ℤ_[p] P.normalization := by
  haveI := fun I => P.residueNormalization_module_finite I
  let ρ : P.normalization →ₗ[ℤ_[p]]
      ∀ I : MaximalSpectrum P.Tensor, integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal) :=
    { toFun := fun x I => ⟨Ideal.Quotient.mk I.asIdeal x,
        IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) (Ideal.Quotient.mk I.asIdeal)
          (RingHom.ext fun _ => rfl) x.2⟩
      map_add' := fun x y => by
        funext I
        exact Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => by
        funext I
        exact Subtype.ext (Submodule.Quotient.mk_smul _ r _) }
  have hρ : Function.Injective ρ := by
    intro x y hxy
    refine Subtype.ext (P.eq_of_forall_residue_eq fun I => ?_)
    exact congrArg Subtype.val (congrFun hxy I)
  haveI : IsNoetherian ℤ_[p] P.normalization := isNoetherian_of_injective ρ hρ
  infer_instance

theorem finite_span_subset_closedBall (s : Set P.Tensor) (hs : s.Finite) :
    ∃ M : ℝ, (Submodule.span ℤ_[p] s : Set P.Tensor) ⊆ Metric.closedBall 0 M := by
  obtain ⟨M, hM⟩ := (hs.image norm).bddAbove
  refine ⟨max M 0, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  induction hx using Submodule.span_induction with
  | mem x hx => exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  | zero => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | smul r x _ hx =>
    change ‖(r : ℚ_[p]) • x‖ ≤ _
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one r)).trans hx

theorem normalization_subset_closedBall :
    ∃ M : ℝ, (P.normalization : Set P.Tensor) ⊆ Metric.closedBall 0 M := by
  letI := P.normalization_module_finite
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := P.normalization)
  obtain ⟨M, hM⟩ := P.finite_span_subset_closedBall
    (P.normalization.val '' (s : Set _)) (s.finite_toSet.image _)
  refine ⟨M, fun x hx => hM ?_⟩
  have hmem : (⟨x, hx⟩ : P.normalization) ∈ Submodule.span ℤ_[p] (s : Set _) :=
    hs ▸ Submodule.mem_top
  have h := Submodule.mem_map_of_mem (f := P.normalization.val.toLinearMap) hmem
  rw [← Submodule.span_image] at h
  exact h

theorem normalization_isBounded : Bornology.IsBounded (P.normalization : Set P.Tensor) := by
  obtain ⟨M, hM⟩ := P.normalization_subset_closedBall
  exact (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M, hM⟩

theorem normalization_isCompact : IsCompact (P.normalization : Set P.Tensor) :=
  Metric.isCompact_of_isClosed_isBounded P.normalization_isClosed P.normalization_isBounded

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
