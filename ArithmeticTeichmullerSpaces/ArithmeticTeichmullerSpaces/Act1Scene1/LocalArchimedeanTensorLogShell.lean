/-
original-paths: refer/iut/Iut/Concrete/LocalConstruct/ArchLogShell.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: b76207ab8955e68a7408d5d2a770b75a30c3bebf
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: use genuine infinite-place tuples, explicit tensor linear
  equivalences, and the proved coordinate/projective norm comparison.
  No LocalTheory or reference admissibility interface is imported.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
source-id: JT-SCENE1-LOCAL-ARCHIMEDEAN-TENSOR-LOG-SHELL
source: the reference file listed above; IUT IV Proposition 1.5(iii),(iv)
and Joshi III `th:thetam-construction` for the intended archimedean component.
fidelity: proves real/complex factor automorphisms are isometries, their
induced tensor maps preserve B_I, and their complete orbit of pi^|I| B_I
is exactly pi^|I| B_I. Proves compactness of this actual region. This is
local tensor infrastructure, not an identification of a paper theta locus.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalArchimedean

open NumberField
open scoped TensorProduct Pointwise ComplexConjugate

universe u
noncomputable section

/-- An `ℝ`-algebra endomorphism of a subalgebra `S` of `ℂ` which is either real (all its
elements are real) or contains `i` preserves the absolute value. -/
theorem norm_algHom_apply_subalgebra (S : Subalgebra ℝ ℂ)
    (hS : Complex.I ∈ S ∨ ∀ x : S, ∃ r : ℝ, (x : ℂ) = r) (σ : S →ₐ[ℝ] S) (x : S) :
    ‖(σ x : ℂ)‖ = ‖(x : ℂ)‖ := by
  rcases hS with hI | hreal
  · set i : S := ⟨Complex.I, hI⟩ with hi
    have hii : i * i = -1 := Subtype.ext (by simp [hi, Complex.I_mul_I])
    have hσi : (σ i : ℂ) ^ 2 = Complex.I ^ 2 := by
      rw [Complex.I_sq, sq, ← Subalgebra.coe_mul, ← map_mul, hii, map_neg, map_one]
      rfl
    have hx : x = algebraMap ℝ S x.1.re + algebraMap ℝ S x.1.im * i := by
      apply Subtype.ext
      simp [hi, Complex.re_add_im]
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hσi
    conv_lhs => rw [hx, map_add, map_mul, σ.commutes, σ.commutes]
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
      Complex.coe_algebraMap]
    rcases hσi with h | h
    · rw [h, Complex.re_add_im]
    · rw [h]
      have : (x.1.re : ℂ) + x.1.im * -Complex.I = conj (x.1 : ℂ) := by
        conv_rhs => rw [← Complex.re_add_im (x.1 : ℂ)]
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
      rw [this, RCLike.norm_conj]
  · obtain ⟨r, hr⟩ := hreal x
    have hx : x = algebraMap ℝ S r := Subtype.ext (by simpa using hr)
    rw [hx, σ.commutes]

variable {K : Type u} [Field K]

/-- The archimedean factor of a real place is real; that of a complex place contains `i`. -/
lemma archField_cases (w : InfinitePlace K) :
    Complex.I ∈ archField w ∨ ∀ x : archField w, ∃ r : ℝ, (x : ℂ) = r := by
  by_cases h : w.IsReal
  · right
    intro x
    have hx : (x : ℂ) ∈ (⊥ : Subalgebra ℝ ℂ) := archField_of_isReal h ▸ x.2
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hx
    exact ⟨r, hr.symm⟩
  · left
    rw [archField_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)]
    exact Algebra.mem_top

variable (v : InfinitePlace K)

/-- The identity map from an archimedean factor to its normed model. -/
def toNormedFactor : Factor v → NormedFactor v := id

/-- **Automorphisms of the archimedean factors are isometries.** -/
theorem norm_archAut_apply (σ : Factor v ≃ₐ[ℝ] Factor v) (x : NormedFactor v) :
    ‖toNormedFactor v (σ x)‖ = ‖x‖ := by
  let σ' : archField v →ₐ[ℝ] archField v :=
    ULift.algEquiv.toAlgHom.comp (σ.toAlgHom.comp ULift.algEquiv.symm.toAlgHom)
  have h := norm_algHom_apply_subalgebra _ (archField_cases v) σ' x.down
  exact h

/-- The automorphism of a factor as a continuous linear map of the normed factor, of norm at
most `1`. -/
noncomputable def archAutCLM (σ : Factor v ≃ₐ[ℝ] Factor v) :
    NormedFactor v →L[ℝ] NormedFactor v :=
  LinearMap.mkContinuous
    { toFun := fun x => toNormedFactor v (σ x)
      map_add' := fun x y => map_add σ x y
      map_smul' := fun r x => map_smul σ r x } 1
    fun x => by rw [one_mul]; exact (norm_archAut_apply v σ x).le

lemma archAutCLM_apply (σ : Factor v ≃ₐ[ℝ] Factor v) (x : NormedFactor v) :
    archAutCLM v σ x = toNormedFactor v (σ x) := rfl

lemma norm_archAutCLM_le (σ : Factor v ≃ₐ[ℝ] Factor v) : ‖archAutCLM v σ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _


variable {ι : Type} [Fintype ι] (c : ι → InfinitePlace K)

def factorTensorAut (σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j)) :
    Tensor c ≃ₗ[ℝ] Tensor c :=
  PiTensorProduct.congr fun j => (σ j).toLinearEquiv

omit [Fintype ι] in
theorem factorTensorAut_tprod (σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j))
    (m : ∀ j, Factor (c j)) :
    factorTensorAut c σ (PiTensorProduct.tprod ℝ m) =
      PiTensorProduct.tprod ℝ (fun j => σ j (m j)) :=
  PiTensorProduct.congr_tprod _ _

theorem toProjectiveModel_factorTensorAut
    (σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j)) (x : Tensor c) :
    toProjectiveModel c (factorTensorAut c σ x) =
      PiTensorProduct.mapL (fun j => archAutCLM (c j) (σ j)) (toProjectiveModel c x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, factorTensorAut_tprod]
    change (r • PiTensorProduct.tprod ℝ (fun j => toNormedFactor (c j) (σ j (m j))) :
        ProjectiveModel c) =
      PiTensorProduct.mapL (fun j => archAutCLM (c j) (σ j))
        (r • PiTensorProduct.tprod ℝ (fun j => toNormedFactor (c j) (m j)) : ProjectiveModel c)
    rw [map_smul, PiTensorProduct.mapL_apply, PiTensorProduct.map_tprod]
    rfl
  | add x y hx hy =>
    rw [map_add]
    change (toProjectiveModel c (factorTensorAut c σ x) +
        toProjectiveModel c (factorTensorAut c σ y) : ProjectiveModel c) =
      PiTensorProduct.mapL (fun j => archAutCLM (c j) (σ j))
        (toProjectiveModel c x + toProjectiveModel c y : ProjectiveModel c)
    rw [map_add, hx, hy]

theorem archNorm_factorTensorAut_le
    (σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j)) (x : Tensor c) :
    archNorm c (factorTensorAut c σ x) ≤ archNorm c x := by
  unfold archNorm
  rw [toProjectiveModel_factorTensorAut]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine (PiTensorProduct.opNorm_mapL _).trans ?_
  exact Finset.prod_le_one (fun j _ => norm_nonneg _)
    (fun j _ => norm_archAutCLM_le (c j) (σ j))

theorem factorTensorAut_image_archIntegral_subset
    (σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j)) :
    factorTensorAut c σ '' archIntegral c ⊆ archIntegral c := by
  rintro _ ⟨x, hx, rfl⟩
  exact (archNorm_factorTensorAut_le c σ x).trans hx

theorem factorTensorAut_image_smul_archIntegral_subset
    (σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j)) (t : ℝ) :
    factorTensorAut c σ '' (t • archIntegral c) ⊆ t • archIntegral c := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨factorTensorAut c σ x,
    factorTensorAut_image_archIntegral_subset c σ ⟨x, hx, rfl⟩, (map_smul _ _ _).symm⟩

def archLogShell : Set (Tensor c) := (Real.pi ^ Fintype.card ι) • archIntegral c

theorem isCompact_archLogShell : IsCompact (archLogShell c) :=
  (isCompact_archIntegral c).smul _

theorem factorTensorAut_image_archLogShell_subset
    (σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j)) :
    factorTensorAut c σ '' archLogShell c ⊆ archLogShell c :=
  factorTensorAut_image_smul_archIntegral_subset c σ _

omit [Fintype ι] in
theorem factorTensorAut_refl (x : Tensor c) :
    factorTensorAut c (fun _ => AlgEquiv.refl) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => rw [map_smul, factorTensorAut_tprod]; rfl
  | add x y hx hy => rw [map_add, hx, hy]

def factorOrbit (S : Set (Tensor c)) : Set (Tensor c) :=
  ⋃ σ : ∀ j, Factor (c j) ≃ₐ[ℝ] Factor (c j), factorTensorAut c σ '' S

theorem factorOrbit_archLogShell : factorOrbit c (archLogShell c) = archLogShell c := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨σ, hx⟩ := Set.mem_iUnion.mp hx
    exact factorTensorAut_image_archLogShell_subset c σ hx
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨fun _ => AlgEquiv.refl,
      ⟨x, hx, factorTensorAut_refl c x⟩⟩

theorem isCompact_factorOrbit_archLogShell : IsCompact (factorOrbit c (archLogShell c)) := by
  rw [factorOrbit_archLogShell]
  exact isCompact_archLogShell c

end
end JoshiTeich.Act1Scene1.LocalArchimedean
