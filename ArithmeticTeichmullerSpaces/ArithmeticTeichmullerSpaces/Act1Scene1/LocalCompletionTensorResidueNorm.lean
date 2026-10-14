/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/ResidueField.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt residue spectral norm and integrality criterion to actual
completion tensors. Expose the spectral NormedField explicitly, without
equating its topology to the tensor coordinate topology or a paper norm.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationDecomposition
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Polynomial.Lifts

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-RESIDUE-SPECTRAL-NORM
source: reviewed reference ResidueField spectral/integrality proofs and
Mathlib spectral norm of algebraic extensions of Q_p.
fidelity: constructs a multiplicative spectral norm extending Q_p, with an
explicit NormedField, and identifies the residue integral closure with its
closed unit ball. Paper C_p norm normalization and topology transfer remain.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open Polynomial
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance normFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance normFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance normTensorFinite : Module.Finite ℚ_[p] P.Tensor :=
  Module.Finite.of_basis P.tensorBasis

instance residueField (I : MaximalSpectrum P.Tensor) : Field (P.Tensor ⧸ I.asIdeal) :=
  Ideal.Quotient.field I.asIdeal

instance residueFieldFinite (I : MaximalSpectrum P.Tensor) :
    Module.Finite ℚ_[p] (P.Tensor ⧸ I.asIdeal) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] I.asIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

def residueNorm (I : MaximalSpectrum P.Tensor) (x : P.Tensor ⧸ I.asIdeal) : ℝ :=
  spectralNorm ℚ_[p] (P.Tensor ⧸ I.asIdeal) x

variable (I : MaximalSpectrum P.Tensor)

theorem residueNorm_nonneg (x : P.Tensor ⧸ I.asIdeal) : 0 ≤ P.residueNorm I x :=
  spectralNorm_nonneg x

theorem residueNorm_zero : P.residueNorm I 0 = 0 := spectralNorm_zero
theorem residueNorm_one : P.residueNorm I 1 = 1 := spectralNorm_one
theorem residueNorm_mul (x y : P.Tensor ⧸ I.asIdeal) :
    P.residueNorm I (x * y) = P.residueNorm I x * P.residueNorm I y :=
  spectralAlgNorm_mul x y

theorem residueNorm_eq_zero_iff {x : P.Tensor ⧸ I.asIdeal} :
    P.residueNorm I x = 0 ↔ x = 0 :=
  ⟨fun h => eq_zero_of_map_spectralNorm_eq_zero h (Algebra.IsAlgebraic.isAlgebraic x),
    fun h => h ▸ P.residueNorm_zero I⟩

theorem residueNorm_pos {x : P.Tensor ⧸ I.asIdeal} (hx : x ≠ 0) : 0 < P.residueNorm I x :=
  lt_of_le_of_ne (P.residueNorm_nonneg I x) (Ne.symm (mt (P.residueNorm_eq_zero_iff I).mp hx))

theorem residueNorm_algebraMap (x : ℚ_[p]) :
    P.residueNorm I (algebraMap ℚ_[p] (P.Tensor ⧸ I.asIdeal) x) = ‖x‖ :=
  spectralNorm_extends x

theorem residueNorm_inv (x : P.Tensor ⧸ I.asIdeal) :
    P.residueNorm I x⁻¹ = (P.residueNorm I x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero, P.residueNorm_zero, inv_zero]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← P.residueNorm_mul, inv_mul_cancel₀ hx, P.residueNorm_one]

theorem isIntegral_iff_residueNorm_le_one (x : P.Tensor ⧸ I.asIdeal) :
    IsIntegral ℤ_[p] x ↔ P.residueNorm I x ≤ 1 := by
  have hmonic : (minpoly ℚ_[p] x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  constructor
  · intro hx
    unfold residueNorm spectralNorm
    rw [spectralValue_le_one_iff hmonic, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hx]
    intro n
    rw [coeff_map, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  · intro hx
    unfold residueNorm spectralNorm at hx
    rw [spectralValue_le_one_iff hmonic] at hx
    have hlift : minpoly ℚ_[p] x ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hx n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlift hmonic
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq]
    exact minpoly.aeval ℚ_[p] x

@[instance_reducible] def residueNormedField : NormedField (P.Tensor ⧸ I.asIdeal) :=
  spectralNorm.normedField ℚ_[p] (P.Tensor ⧸ I.asIdeal)

theorem residueNormedField_norm (x : P.Tensor ⧸ I.asIdeal) :
    letI := P.residueNormedField I
    ‖x‖ = P.residueNorm I x := rfl

theorem residueIntegralClosure_eq_closedBall :
    letI := P.residueNormedField I
    letI : PseudoMetricSpace (P.Tensor ⧸ I.asIdeal) :=
      (P.residueNormedField I).toMetricSpace.toPseudoMetricSpace
    (integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal) : Set (P.Tensor ⧸ I.asIdeal)) =
      Metric.closedBall 0 1 := by
  letI := P.residueNormedField I
  letI : PseudoMetricSpace (P.Tensor ⧸ I.asIdeal) :=
    (P.residueNormedField I).toMetricSpace.toPseudoMetricSpace
  ext x
  change IsIntegral ℤ_[p] x ↔ P.residueNorm I (x - 0) ≤ 1
  rw [sub_zero]
  exact P.isIntegral_iff_residueNorm_le_one I x

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
