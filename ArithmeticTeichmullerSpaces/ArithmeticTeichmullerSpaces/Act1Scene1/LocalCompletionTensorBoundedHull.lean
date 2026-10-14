/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/Hull.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt coordinate-supremum least-hull construction to bounded
actual tensor subsets of positive normalization Haar; derive topology and
Haar bounds using the constructed normalization and finite-dimensional maps.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueBounds
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHaarSubspaces
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorPrincipalRegions

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-BOUNDED-LEAST-HULL
source: reviewed reference Hull coordinate-supremum construction and Joshi III
componentwise principal hull shape (3568--3574).
fidelity: constructs least principal normalization hulls for arbitrary bounded
positive-Haar tensor regions; proves principal hulls compact and open in the
actual tensor topology. No paper theta-region or weighted-volume identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
open scoped Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance hullFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance hullFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance hullTensorFinite : Module.Finite ℚ_[p] P.Tensor :=
  Module.Finite.of_basis P.tensorBasis

def principalLinearEquiv (a : P.Tensor) (ha : IsUnit a) : P.Tensor ≃ₗ[ℚ_[p]] P.Tensor where
  toFun x := a * x
  invFun x := ↑ha.unit⁻¹ * x
  left_inv x := by
    change ↑ha.unit⁻¹ * (a * x) = x
    rw [← mul_assoc, ha.val_inv_mul, one_mul]
  right_inv x := by
    change a * (↑ha.unit⁻¹ * x) = x
    rw [← mul_assoc, ha.mul_val_inv, one_mul]
  map_add' := mul_add a
  map_smul' r x := by
    change a * (r • x) = r • (a * x)
    rw [mul_smul_comm]

theorem principalRegion_isCompact (a : P.Tensor) (ha : IsUnit a) :
    IsCompact (P.principalRegion a) :=
  P.normalization_isCompact.image (P.principalLinearEquiv a ha).toContinuousLinearEquiv.continuous

theorem principalRegion_isOpen (a : P.Tensor) (ha : IsUnit a) :
    IsOpen (P.principalRegion a) :=
  (P.principalLinearEquiv a ha).toContinuousLinearEquiv.toHomeomorph.isOpenMap _ P.normalization_isOpen

theorem principalRegion_haar_pos_lt_top (a : P.Tensor) (ha : IsUnit a) :
    0 < P.normalizationHaar (P.principalRegion a) ∧
      P.normalizationHaar (P.principalRegion a) < ⊤ := by
  exact ⟨(P.principalRegion_isOpen a ha).measure_pos _ ⟨0, 0, P.normalization.zero_mem, mul_zero _⟩,
    (P.principalRegion_isCompact a ha).measure_lt_top⟩

theorem exists_least_bounded_principalHull (U : Set P.Tensor)
    (hU : Bornology.IsBounded U)
    (hcoord : ∀ I : MaximalSpectrum P.Tensor, ∃ x ∈ U, Ideal.Quotient.mk I.asIdeal x ≠ 0) :
    ∃ a : P.Tensor, IsUnit a ∧ U ⊆ P.principalRegion a ∧
      ∀ b : P.Tensor, IsUnit b → U ⊆ P.principalRegion b →
        P.principalRegion a ⊆ P.principalRegion b := by
  obtain ⟨B, hB⟩ := P.exists_uniform_residueNorm_bound hU
  let M := fun I : MaximalSpectrum P.Tensor =>
    sSup ((fun x => P.residueNorm I (Ideal.Quotient.mk I.asIdeal x)) '' U)
  have hbound (I : MaximalSpectrum P.Tensor) :
      BddAbove ((fun x => P.residueNorm I (Ideal.Quotient.mk I.asIdeal x)) '' U) :=
    ⟨B, by rintro _ ⟨x, hx, rfl⟩; exact hB x hx I⟩
  have hle (I : MaximalSpectrum P.Tensor) (x : P.Tensor) (hx : x ∈ U) :
      P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) ≤ M I :=
    le_csSup (hbound I) ⟨x, hx, rfl⟩
  have hpos (I : MaximalSpectrum P.Tensor) : 0 < M I := by
    obtain ⟨x, hx, hx0⟩ := hcoord I
    exact (P.residueNorm_pos I hx0).trans_le (hle I x hx)
  have hsup (I : MaximalSpectrum P.Tensor) (t : ℝ)
      (ht : ∀ x ∈ U, P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) ≤ t) : M I ≤ t := by
    obtain ⟨x, hx, _⟩ := hcoord I
    exact csSup_le ⟨_, x, hx, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact ht y hy)
  obtain ⟨a, ha, hMa, hmin⟩ := P.exists_least_principalRegion_of_radii M hpos
  refine ⟨a, ha, fun x hx => (P.mem_principalRegion_iff a ha x).mpr
    (fun I => (hle I x hx).trans (hMa I)), ?_⟩
  intro b hb hUb
  exact hmin b hb fun I => hsup I _ fun x hx =>
    (P.mem_principalRegion_iff b hb x).mp (hUb hx) I

theorem exists_least_positiveHaar_hull (U : Set P.Tensor)
    (hU : Bornology.IsBounded U) (hpos : 0 < P.normalizationHaar U) :
    ∃ a : P.Tensor, IsUnit a ∧ U ⊆ P.principalRegion a ∧
      IsCompact (P.principalRegion a) ∧ IsOpen (P.principalRegion a) ∧
      (0 < P.normalizationHaar (P.principalRegion a) ∧
        P.normalizationHaar (P.principalRegion a) < ⊤) ∧
      ∀ b : P.Tensor, IsUnit b → U ⊆ P.principalRegion b →
        P.principalRegion a ⊆ P.principalRegion b := by
  obtain ⟨a, ha, hUa, hmin⟩ := P.exists_least_bounded_principalHull U hU
    (fun I => P.exists_residue_ne_zero_of_haar_pos hpos I)
  exact ⟨a, ha, hUa, P.principalRegion_isCompact a ha, P.principalRegion_isOpen a ha,
    P.principalRegion_haar_pos_lt_top a ha, hmin⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
