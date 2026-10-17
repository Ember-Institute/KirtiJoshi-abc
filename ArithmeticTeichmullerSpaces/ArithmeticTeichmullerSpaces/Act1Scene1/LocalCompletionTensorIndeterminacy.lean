/-
original-paths: refer/iut/Iut/Concrete/LocalConstruct/Indeterminacy.lean,
  refer/iut/Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: b76207ab8955e68a7408d5d2a770b75a30c3bebf
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: use actual completion Packet factors, their existing tensor topology,
  algebra equivalences and actual integral closure. Only finite-place factor
  automorphisms are adapted; no reference LocalTheory or theta-pilot is imported.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHaar
import Mathlib.FieldTheory.Fixed

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-FACTOR-INDETERMINACY
source: the two reference files listed above; IUT IV Proposition 1.4(iv),
and Joshi III `th:thetam-construction` / `pr:convexes-and-hulls`.
fidelity: constructs the finite family of tensor automorphisms induced by
actual completion-factor automorphisms. Their finite orbit of a compact set
is compact, and its positive Haar measure remains finite. They preserve the
actual normalization. This does not identify them with all paper indeterminacies
or identify their orbit with a theta-values locus.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
open scoped TensorProduct

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance indFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance indFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance indFactorAutFintype (i : ι) :
    Fintype (P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :=
  AlgEquiv.fintype ℚ_[p] (P.Factor i)

def factorTensorMap (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    P.Tensor →ₐ[ℚ_[p]] P.Tensor :=
  PiTensorProduct.liftAlgHom
    ((PiTensorProduct.tprod ℚ_[p]).compLinearMap fun i => (σ i).toLinearMap)
    (by
      rw [MultilinearMap.compLinearMap_apply, PiTensorProduct.one_def]
      congr 1
      funext i
      exact map_one (σ i))
    (by
      intro x y
      simp only [MultilinearMap.compLinearMap_apply, AlgEquiv.toLinearMap_apply,
        PiTensorProduct.tprod_mul_tprod]
      congr 1
      funext i
      exact map_mul (σ i) (x i) (y i))

theorem factorTensorMap_tprod (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i)
    (a : ∀ i, P.Factor i) :
    P.factorTensorMap σ (PiTensorProduct.tprod ℚ_[p] a) =
      PiTensorProduct.tprod ℚ_[p] (fun i => σ i (a i)) := by
  unfold factorTensorMap
  rw [PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  rfl

theorem factorTensorMap_bijective (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    Function.Bijective (P.factorTensorMap σ) := by
  change Function.Bijective (PiTensorProduct.congr (fun i => (σ i).toLinearEquiv))
  exact (PiTensorProduct.congr (fun i => (σ i).toLinearEquiv)).bijective

def factorTensorAut (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    P.Tensor ≃ₐ[ℚ_[p]] P.Tensor :=
  AlgEquiv.ofBijective (P.factorTensorMap σ) (P.factorTensorMap_bijective σ)

theorem factorTensorMap_refl :
    P.factorTensorMap (fun _ => AlgEquiv.refl) = AlgHom.id _ _ := by
  classical
  refine PiTensorProduct.algHom_ext fun i => ?_
  ext a
  simp only [AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply,
    factorTensorMap_tprod, AlgHom.id_apply, AlgEquiv.coe_refl, id_eq]

theorem factorTensorAut_continuous (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    Continuous (P.factorTensorAut σ) :=
  (P.factorTensorAut σ).toLinearMap.continuous_of_finiteDimensional

private theorem tensorAut_map_normalization (e : P.Tensor ≃ₐ[ℚ_[p]] P.Tensor)
    {x : P.Tensor} (hx : x ∈ P.normalization) : e x ∈ P.normalization := by
  exact IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) e.toRingHom
    (RingHom.ext fun r => (e.commutes (r : ℚ_[p])).symm) hx

theorem factorTensorAut_image_normalization
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    (P.factorTensorAut σ) '' (P.normalization : Set P.Tensor) = P.normalization := by
  let e := P.factorTensorAut σ
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact P.tensorAut_map_normalization e hx
  · intro x hx
    exact ⟨e.symm x, P.tensorAut_map_normalization e.symm hx, e.apply_symm_apply x⟩

def factorIndeterminacies : Set (P.Tensor → P.Tensor) :=
  Set.range (fun σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i =>
    (P.factorTensorAut σ : P.Tensor → P.Tensor))

theorem factorIndeterminacies_finite : P.factorIndeterminacies.Finite :=
  Set.finite_range _

theorem id_mem_factorIndeterminacies : id ∈ P.factorIndeterminacies := by
  refine ⟨fun _ => AlgEquiv.refl, ?_⟩
  change (P.factorTensorMap (fun _ => AlgEquiv.refl) : P.Tensor → P.Tensor) = id
  rw [P.factorTensorMap_refl]
  rfl

theorem continuous_of_mem_factorIndeterminacies
    {φ : P.Tensor → P.Tensor} (hφ : φ ∈ P.factorIndeterminacies) : Continuous φ := by
  obtain ⟨σ, rfl⟩ := hφ
  exact P.factorTensorAut_continuous σ

def factorIndeterminacyOrbit (S : Set P.Tensor) : Set P.Tensor :=
  ⋃ φ ∈ P.factorIndeterminacies, φ '' S

theorem subset_factorIndeterminacyOrbit (S : Set P.Tensor) :
    S ⊆ P.factorIndeterminacyOrbit S := by
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨id, P.id_mem_factorIndeterminacies, ⟨x, hx, rfl⟩⟩

theorem factorIndeterminacyOrbit_isCompact {S : Set P.Tensor} (hS : IsCompact S) :
    IsCompact (P.factorIndeterminacyOrbit S) :=
  P.factorIndeterminacies_finite.isCompact_biUnion fun φ hφ =>
    hS.image (P.continuous_of_mem_factorIndeterminacies hφ)

theorem factorIndeterminacyOrbit_haar_pos_lt_top {S : Set P.Tensor}
    (hS : IsCompact S) (hpos : 0 < P.normalizationHaar S) :
    0 < P.normalizationHaar (P.factorIndeterminacyOrbit S) ∧
      P.normalizationHaar (P.factorIndeterminacyOrbit S) < ⊤ :=
  ⟨hpos.trans_le (measure_mono (P.subset_factorIndeterminacyOrbit S)),
    (P.factorIndeterminacyOrbit_isCompact hS).measure_lt_top⟩

theorem factorIndeterminacyOrbit_normalization :
    P.factorIndeterminacyOrbit P.normalization = P.normalization := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨σ, rfl⟩ := hφ
    rw [P.factorTensorAut_image_normalization σ] at hx
    exact hx
  · exact P.subset_factorIndeterminacyOrbit _

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
