import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogFunctoriality
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorSaturatedLogShell

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-LOG-SHELL-INDETERMINACY
source: reference LocalConstruct/LogShell, mapAlgHom_image_logShell_subset
and indAut_logShell; IUT IV Proposition 1.2 and Joshi III tensor log-shells.
fidelity: proves actual completion-factor automorphisms preserve ordinary
factor shells by continuity and log functoriality. Their tensor maps preserve
the ordinary tensor shell and its normalization saturation. The full finite
factor orbit of the saturated shell equals that shell, hence has positive
finite actual Haar. No BK or paper Ind1--Ind3 identity is asserted.
Original tensor consumer proofs; no reference source code copied here.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
open scoped TensorProduct Classical

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance autFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance autFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance autFactorContinuousSMul (i : ι) : ContinuousSMul ℚ_[p] (P.Factor i) :=
  continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb (P.residueChar_eq i))
local instance autFactorCharZero (i : ι) : CharZero (P.Factor i) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding (P.place i).maximalIdeal).injective
local instance autIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

omit [Fintype ι] in
theorem factorAut_image_logShell_subset (i : ι) (σ : P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    σ '' LocalPadicLog.logShell (k := P.Factor i) p ⊆ LocalPadicLog.logShell p := by
  have hp : ‖(p : P.Factor i)‖ < 1 := by
    have h := norm_natCast_prime_lt_one (P.residueChar_eq i)
    rwa [← NumberField.FinitePlace.embedding_apply, map_natCast] at h
  exact LocalPadicLog.image_logShell_subset (Fact.out : p.Prime) hp σ.toRingHom
    σ.toLinearMap.continuous_of_finiteDimensional

theorem factorTensorAut_mem_tensorLogShell
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) {x : P.Tensor}
    (hx : x ∈ P.tensorLogShell) : P.factorTensorAut σ x ∈ P.tensorLogShell := by
  induction hx using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, rfl⟩ := ht
    change P.factorTensorMap σ (P.pure a) ∈ P.tensorLogShell
    rw [pure, P.factorTensorMap_tprod]
    exact P.pure_mem_lattice _ _ fun i =>
      P.factorAut_image_logShell_subset i (σ i) ⟨a i, ha i, rfl⟩
  | zero => rw [map_zero]; exact P.tensorLogShell.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact P.tensorLogShell.add_mem hx hy
  | smul r x _ hx =>
    change P.factorTensorAut σ ((r : ℚ_[p]) • x) ∈ P.tensorLogShell
    rw [map_smul]
    exact P.tensorLogShell.smul_mem r hx

theorem factorTensorAut_mem_saturatedLogShell
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) {x : P.Tensor}
    (hx : x ∈ P.saturatedLogShell) : P.factorTensorAut σ x ∈ P.saturatedLogShell := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    exact P.tensorLogShell_subset_saturatedLogShell (P.factorTensorAut_mem_tensorLogShell σ hx)
  | zero => rw [map_zero]; exact P.saturatedLogShell.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact P.saturatedLogShell.add_mem hx hy
  | smul r x _ hx =>
    change P.factorTensorAut σ ((r : P.Tensor) * x) ∈ P.saturatedLogShell
    rw [map_mul]
    apply P.saturatedLogShell_mul_mem _ hx
    exact (P.factorTensorAut_image_normalization σ).subset ⟨r, r.2, rfl⟩

theorem factorTensorAut_apply_inverse_family
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) (x : P.Tensor) :
    P.factorTensorAut σ (P.factorTensorAut (fun i => (σ i).symm) x) = x := by
  change (PiTensorProduct.congr (fun i => (σ i).toLinearEquiv))
    ((PiTensorProduct.congr (fun i => (σ i).toLinearEquiv)).symm x) = x
  exact LinearEquiv.apply_symm_apply _ x

theorem factorTensorAut_image_saturatedLogShell
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    P.factorTensorAut σ '' (P.saturatedLogShell : Set P.Tensor) = P.saturatedLogShell := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact P.factorTensorAut_mem_saturatedLogShell σ hx
  · intro x hx
    exact ⟨P.factorTensorAut (fun i => (σ i).symm) x,
      P.factorTensorAut_mem_saturatedLogShell _ hx, P.factorTensorAut_apply_inverse_family σ x⟩

theorem factorIndeterminacyOrbit_saturatedLogShell :
    P.factorIndeterminacyOrbit P.saturatedLogShell = P.saturatedLogShell := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨φ, hφ, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨σ, rfl⟩ := hφ
    rw [P.factorTensorAut_image_saturatedLogShell σ] at hx
    exact hx
  · exact P.subset_factorIndeterminacyOrbit _

theorem factorIndeterminacyOrbit_saturatedLogShell_haar_pos_lt_top :
    0 < P.normalizationHaar (P.factorIndeterminacyOrbit P.saturatedLogShell) ∧
      P.normalizationHaar (P.factorIndeterminacyOrbit P.saturatedLogShell) < ⊤ := by
  rw [P.factorIndeterminacyOrbit_saturatedLogShell]
  exact P.saturatedLogShell_haar_pos_lt_top

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
