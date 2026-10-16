import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Topology.LocallyConstant.Basic

/-!
source-id: JT-SCENE1-LOCALLY-CONSTANT-GALOIS-HILBERT90
source: Krull finite Galois neighbourhoods, Galois fixed-field descent and
Mathlib's finite-extension Hilbert 90.
fidelity: any locally constant multiplicative cocycle on the actual Galois
group of an algebraic Galois extension is a coboundary in that extension.
The finite intermediate field and coboundary witness are derived, not inputs.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.GaloisCocycle
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [IsGalois K Ω]

theorem locallyConstant_hilbert90 (f : (Ω ≃ₐ[K] Ω) → Ωˣ)
    (hloc : IsLocallyConstant f) (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f := by
  have hU : {σ | f σ = 1} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
    (hloc.isOpen_fiber 1).mem_nhds (groupCohomology.map_one_of_isMulCocycle₁ hf)
  obtain ⟨L, hL⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois _).mp hU
  let res : (Ω ≃ₐ[K] Ω) →* (L ≃ₐ[K] L) :=
    AlgEquiv.restrictNormalHom (L : IntermediateField K Ω)
  have hker (σ : Ω ≃ₐ[K] Ω) (hσ : res σ = 1) : f σ = 1 := by
    apply hL
    rw [← (L : IntermediateField K Ω).restrictNormalHom_ker]
    exact hσ
  have hfactor (σ τ : Ω ≃ₐ[K] Ω) (h : res σ = res τ) : f σ = f τ := by
    have hk : res (τ⁻¹ * σ) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have he := hf τ (τ⁻¹ * σ)
    simpa only [mul_inv_cancel_left, hker _ hk, smul_one, one_mul] using he
  have hmem (σ : Ω ≃ₐ[K] Ω) : (f σ : Ω) ∈ (L : IntermediateField K Ω) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (L : IntermediateField K Ω)]
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hk : res τ = 1 := by
      change τ ∈ res.ker
      rwa [(L : IntermediateField K Ω).restrictNormalHom_ker]
    have he := hf τ σ
    have heq : f (τ * σ) = f σ := hfactor _ _ (by rw [map_mul, hk, one_mul])
    rw [heq, hker τ hk, mul_one] at he
    exact (congrArg (fun x : Ωˣ => (x : Ω)) he).symm
  let lift (σ : L ≃ₐ[K] L) : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
  have hlift (σ : L ≃ₐ[K] L) : res (lift σ) = σ := AlgEquiv.restrict_liftNormal Ω σ
  let F (σ : L ≃ₐ[K] L) : Lˣ :=
    { val := ⟨f (lift σ), hmem _⟩
      inv := ⟨(f (lift σ) : Ω)⁻¹, (L : IntermediateField K Ω).inv_mem (hmem _)⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ (f (lift σ)).ne_zero)
      inv_val := Subtype.ext (inv_mul_cancel₀ (f (lift σ)).ne_zero) }
  have hcomm (σ : L ≃ₐ[K] L) (x : L) :
      ((σ x : L) : Ω) = lift σ (x : Ω) := by
    have h := AlgEquiv.restrictNormal_commutes (lift σ) (L : IntermediateField K Ω) x
    change ((res (lift σ)) x : Ω) = lift σ (x : Ω) at h
    rw [hlift] at h
    exact h
  have hF : groupCohomology.IsMulCocycle₁ F := by
    intro σ τ
    apply Units.ext
    apply Subtype.ext
    change (f (lift (σ * τ)) : Ω) = ((σ (F τ : L) : L) : Ω) * (f (lift σ) : Ω)
    rw [hcomm]
    have he := hfactor (lift (σ * τ)) (lift σ * lift τ)
      (by rw [hlift, map_mul, hlift, hlift])
    rw [he, hf]
    rfl
  obtain ⟨b, hb⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units F hF
  let B : Ωˣ := Units.map (L : IntermediateField K Ω).subtype.toMonoidHom b
  refine ⟨B, fun σ => ?_⟩
  apply Units.ext
  have h := congrArg (fun x : Lˣ => ((x : L) : Ω)) (hb (res σ))
  simp only [Units.val_div_eq_div_val, IntermediateField.coe_div] at h
  change ((res σ (b : L) : L) : Ω) / ((b : L) : Ω) = (f (lift (res σ)) : Ω) at h
  have hres : ((res σ (b : L) : L) : Ω) = σ ((b : L) : Ω) :=
    AlgEquiv.restrictNormal_commutes σ (L : IntermediateField K Ω) (b : L)
  rw [hres, hfactor _ σ (hlift (res σ))] at h
  have hB : (B : Ω) = ((b : L) : Ω) := rfl
  have hσB : ((σ • B : Ωˣ) : Ω) = σ (B : Ω) := rfl
  rw [Units.val_div_eq_div_val, hσB, hB]
  exact h

end
end JoshiTeich.Act1Scene1.GaloisCocycle
