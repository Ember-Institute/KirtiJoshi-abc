/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/ResidueField.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt unit and principal-region norm criteria; derive least
componentwise radii from actual spectral discreteness and residue decomposition.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueNormDiscrete
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueBallRegions
import Mathlib.Algebra.Group.Pi.Units

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-PRINCIPAL-RADIUS-MINIMUM
source: reviewed reference residue unit/principal-region criteria; Joshi III
3568--3574 and actual least attainable residue spectral norms.
fidelity: constructs principal normalization regions and the least region
whose residue radii dominate a prescribed positive coordinate family. The
bounds of an arbitrary set and their positivity are not supplied automatically.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open scoped Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

theorem isUnit_iff_residue_ne_zero (a : P.Tensor) :
    IsUnit a ↔ ∀ I : MaximalSpectrum P.Tensor, Ideal.Quotient.mk I.asIdeal a ≠ 0 := by
  constructor
  · intro ha I
    exact (ha.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
  · intro h
    have hu : IsUnit (P.residueDecomposition a) :=
      (Pi.isUnit_iff).mpr fun I => isUnit_iff_ne_zero.mpr (h I)
    simpa using hu.map P.residueDecomposition.symm

def principalRegion (a : P.Tensor) : Set P.Tensor :=
  (fun y => a * y) '' (P.normalization : Set P.Tensor)

theorem mem_principalRegion_iff (a : P.Tensor) (ha : IsUnit a) (x : P.Tensor) :
    x ∈ P.principalRegion a ↔ ∀ I : MaximalSpectrum P.Tensor,
      P.residueNorm I (Ideal.Quotient.mk I.asIdeal x) ≤
        P.residueNorm I (Ideal.Quotient.mk I.asIdeal a) := by
  change x ∈ ((fun y => a * y) '' (P.normalization : Set P.Tensor)) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩ I
    rw [map_mul, P.residueNorm_mul]
    exact mul_le_of_le_one_right (P.residueNorm_nonneg I _)
      ((P.mem_normalization_iff_residueNorm_le_one y).mp hy I)
  · intro h
    refine ⟨↑ha.unit⁻¹ * x, ?_, ?_⟩
    · change (↑ha.unit⁻¹ * x : P.Tensor) ∈ P.normalization
      rw [P.mem_normalization_iff_residueNorm_le_one]
      intro I
      have hne := (P.isUnit_iff_residue_ne_zero a).mp ha I
      have hinv : Ideal.Quotient.mk I.asIdeal ↑ha.unit⁻¹ =
          (Ideal.Quotient.mk I.asIdeal a)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_mul, ha.val_inv_mul, map_one]
      rw [map_mul, P.residueNorm_mul, hinv, P.residueNorm_inv,
        inv_mul_le_iff₀ (P.residueNorm_pos I hne), mul_one]
      exact h I
    · change a * (↑ha.unit⁻¹ * x) = x
      rw [← mul_assoc, ha.mul_val_inv, one_mul]

theorem exists_least_principalRegion_of_radii
    (M : MaximalSpectrum P.Tensor → ℝ) (hM : ∀ I, 0 < M I) :
    ∃ a : P.Tensor, IsUnit a ∧
      (∀ I, M I ≤ P.residueNorm I (Ideal.Quotient.mk I.asIdeal a)) ∧
      ∀ b : P.Tensor, IsUnit b →
        (∀ I, M I ≤ P.residueNorm I (Ideal.Quotient.mk I.asIdeal b)) →
        P.principalRegion a ⊆ P.principalRegion b := by
  choose c hc0 hcM hcmin using fun I => P.exists_least_residueNorm_ge I (hM I)
  let a := P.residueDecomposition.symm c
  have hcoords (I : MaximalSpectrum P.Tensor) : Ideal.Quotient.mk I.asIdeal a = c I :=
    congrFun (P.residueDecomposition.apply_symm_apply c) I
  have ha : IsUnit a := (P.isUnit_iff_residue_ne_zero a).mpr fun I => by
    rw [hcoords I]
    exact hc0 I
  refine ⟨a, ha, fun I => by rw [hcoords I]; exact hcM I, ?_⟩
  intro b hb hMb x hx
  rw [P.mem_principalRegion_iff b hb x]
  have hxa := (P.mem_principalRegion_iff a ha x).mp hx
  intro I
  refine (hxa I).trans ?_
  rw [hcoords I]
  exact hcmin I _ ((P.isUnit_iff_residue_ne_zero b).mp hb I) (hMb I)

theorem exists_least_integral_principalHull (U : Set P.Tensor)
    (hU : U ⊆ P.normalization)
    (hcoord : ∀ I : MaximalSpectrum P.Tensor, ∃ x ∈ U, Ideal.Quotient.mk I.asIdeal x ≠ 0) :
    ∃ a : P.Tensor, IsUnit a ∧ a ∈ P.normalization ∧ U ⊆ P.principalRegion a ∧
      ∀ b : P.Tensor, IsUnit b → U ⊆ P.principalRegion b →
        P.principalRegion a ⊆ P.principalRegion b := by
  let M := fun I : MaximalSpectrum P.Tensor =>
    sSup ((fun x => P.residueNorm I (Ideal.Quotient.mk I.asIdeal x)) '' U)
  have hbound (I : MaximalSpectrum P.Tensor) :
      BddAbove ((fun x => P.residueNorm I (Ideal.Quotient.mk I.asIdeal x)) '' U) :=
    ⟨1, by rintro _ ⟨x, hx, rfl⟩; exact (P.mem_normalization_iff_residueNorm_le_one x).mp (hU hx) I⟩
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
  have hUa : U ⊆ P.principalRegion a := fun x hx =>
    (P.mem_principalRegion_iff a ha x).mpr fun I => (hle I x hx).trans (hMa I)
  have hone : ∀ I, M I ≤ P.residueNorm I (Ideal.Quotient.mk I.asIdeal (1 : P.Tensor)) := by
    intro I
    rw [map_one, P.residueNorm_one]
    exact hsup I 1 fun x hx => (P.mem_normalization_iff_residueNorm_le_one x).mp (hU hx) I
  have hane : a ∈ P.normalization := by
    have haRegion : a ∈ P.principalRegion a := ⟨1, P.normalization.one_mem, mul_one _⟩
    have h := hmin 1 isUnit_one hone haRegion
    obtain ⟨y, hy, hya⟩ := h
    have hya' : y = a := by simpa only [one_mul] using hya
    exact hya' ▸ hy
  refine ⟨a, ha, hane, hUa, ?_⟩
  intro b hb hUb
  exact hmin b hb fun I => hsup I _ fun x hx =>
    (P.mem_principalRegion_iff b hb x).mp (hUb hx) I

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
