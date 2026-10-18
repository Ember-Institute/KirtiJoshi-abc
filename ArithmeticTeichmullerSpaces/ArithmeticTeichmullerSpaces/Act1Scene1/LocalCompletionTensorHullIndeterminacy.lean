import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorPointOrbitHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorLogShellIndeterminacy
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarDeterminant

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-HULL-INDETERMINACY
source: reference LocalConstruct/Indeterminacy's span transport and
ThetaRegion's factor images; Joshi III principal hull / convex-hull comparison.
fidelity: actual factor automorphisms compose, their orbit is invariant and
idempotent, normalization spans transport, and orbit-generated hulls are
invariant. Normalization Haar is preserved on every set, proved using the
actual determinant modulus and normalization measure one.
Original proofs; no reference source code copied.
boundary: Scene1/Derived; no full paper Ind1--Ind3 or theta identity.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
open scoped Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance hullAutFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance hullAutFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance hullAutIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem factorTensorAut_comp_family
    (σ τ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) (x : P.Tensor) :
    P.factorTensorAut σ (P.factorTensorAut τ x) =
      P.factorTensorAut (fun i => (τ i).trans (σ i)) x := by
  have h : (P.factorTensorAut σ).toAlgHom.comp (P.factorTensorAut τ).toAlgHom =
      (P.factorTensorAut (fun i => (τ i).trans (σ i))).toAlgHom := by
    apply PiTensorProduct.algHom_ext
    intro i
    ext a
    simp only [AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply]
    change P.factorTensorMap σ (P.factorTensorMap τ _) = P.factorTensorMap _ _
    simp only [P.factorTensorMap_tprod, AlgEquiv.trans_apply]
  exact congrArg (fun f => f x) h

theorem factorTensorAut_image_orbit_subset
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) (U : Set P.Tensor) :
    P.factorTensorAut σ '' P.factorIndeterminacyOrbit U ⊆ P.factorIndeterminacyOrbit U := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hf, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨τ, rfl⟩ := hf
  exact Set.mem_iUnion₂.mpr ⟨_, ⟨fun i => (τ i).trans (σ i), rfl⟩,
    ⟨y, hy, (P.factorTensorAut_comp_family σ τ y).symm⟩⟩

theorem factorTensorAut_image_orbit
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) (U : Set P.Tensor) :
    P.factorTensorAut σ '' P.factorIndeterminacyOrbit U = P.factorIndeterminacyOrbit U := by
  apply Set.Subset.antisymm (P.factorTensorAut_image_orbit_subset σ U)
  intro x hx
  exact ⟨P.factorTensorAut (fun i => (σ i).symm) x,
    P.factorTensorAut_image_orbit_subset _ U ⟨x, hx, rfl⟩,
    P.factorTensorAut_apply_inverse_family σ x⟩

theorem factorIndeterminacyOrbit_idem (U : Set P.Tensor) :
    P.factorIndeterminacyOrbit (P.factorIndeterminacyOrbit U) = P.factorIndeterminacyOrbit U := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨f, hf, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨σ, rfl⟩ := hf
    exact P.factorTensorAut_image_orbit_subset σ U hx
  · exact P.subset_factorIndeterminacyOrbit _

theorem factorTensorAut_image_normalizationHull_subset
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) {U V : Set P.Tensor}
    (hUV : P.factorTensorAut σ '' U ⊆ V) :
    P.factorTensorAut σ '' (P.normalizationHull U : Set P.Tensor) ⊆ P.normalizationHull V := by
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact P.subset_normalizationHull V (hUV ⟨x, hx, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    change P.factorTensorAut σ ((r : P.Tensor) * x) ∈ P.normalizationHull V
    rw [map_mul]
    have hr : P.factorTensorAut σ r ∈ (P.normalization : Set P.Tensor) :=
      (P.factorTensorAut_image_normalization σ).subset ⟨r, r.2, rfl⟩
    exact (P.normalizationHull V).smul_mem (⟨P.factorTensorAut σ r, hr⟩ : P.normalization) hx

theorem factorTensorAut_image_orbitHull
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) (U : Set P.Tensor) :
    P.factorTensorAut σ '' (P.normalizationHull (P.factorIndeterminacyOrbit U) : Set P.Tensor) =
      P.normalizationHull (P.factorIndeterminacyOrbit U) := by
  have hin (τ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :=
    P.factorTensorAut_image_normalizationHull_subset τ (P.factorTensorAut_image_orbit_subset τ U)
  apply Set.Subset.antisymm (hin σ)
  intro x hx
  exact ⟨P.factorTensorAut (fun i => (σ i).symm) x, hin _ ⟨x, hx, rfl⟩,
    P.factorTensorAut_apply_inverse_family σ x⟩

theorem factorIndeterminacyOrbit_orbitHull (U : Set P.Tensor) :
    P.factorIndeterminacyOrbit (P.normalizationHull (P.factorIndeterminacyOrbit U)) =
      (P.normalizationHull (P.factorIndeterminacyOrbit U) : Set P.Tensor) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨f, hf, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨σ, rfl⟩ := hf
    exact (P.factorTensorAut_image_orbitHull σ U).subset hx
  · exact P.subset_factorIndeterminacyOrbit _

theorem factorTensorAut_det_norm
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    ‖LinearMap.det (P.factorTensorAut σ).toLinearMap‖ = 1 := by
  let f := (P.factorTensorAut σ).toLinearEquiv.toContinuousLinearEquiv
  have h := PadicHaar.measure_image_linearEquiv_eq_norm_det P.normalizationHaar f
    (P.normalization : Set P.Tensor)
  change P.normalizationHaar ((P.factorTensorAut σ) '' (P.normalization : Set P.Tensor)) =
    ENNReal.ofReal ‖LinearMap.det (P.factorTensorAut σ).toLinearMap‖ *
      P.normalizationHaar P.normalization at h
  rw [P.factorTensorAut_image_normalization, P.normalizationHaar_normalization, mul_one] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal (norm_nonneg _)] using hr.symm

theorem normalizationHaar_factorTensorAut_image
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) (U : Set P.Tensor) :
    P.normalizationHaar (P.factorTensorAut σ '' U) = P.normalizationHaar U := by
  have h := PadicHaar.measure_image_linearEquiv_eq_norm_det P.normalizationHaar
    (P.factorTensorAut σ).toLinearEquiv.toContinuousLinearEquiv U
  change P.normalizationHaar (P.factorTensorAut σ '' U) =
    ENNReal.ofReal ‖LinearMap.det (P.factorTensorAut σ).toLinearMap‖ * P.normalizationHaar U at h
  simpa only [P.factorTensorAut_det_norm, ENNReal.ofReal_one, one_mul] using h

theorem normalizationLogVolume_factorTensorAut_image
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) (U : Set P.Tensor) :
    P.normalizationLogVolume (P.factorTensorAut σ '' U) = P.normalizationLogVolume U := by
  unfold normalizationLogVolume
  rw [P.normalizationHaar_factorTensorAut_image]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
