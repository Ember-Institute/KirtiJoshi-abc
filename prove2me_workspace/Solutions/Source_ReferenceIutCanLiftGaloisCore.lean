/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/GaloisClosure.lean
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationGalois

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

universe u

open IntermediateField

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
variable {N : IntermediateField (rationalBase k t) Ω}

/-- The intersection of conjugates of `Gal(N/L)` by elements of `Gal(N/F)`. -/
def galoisCore (F L : IntermediateField (rationalBase k t) Ω) :
    Subgroup (N ≃ₐ[rationalBase k t] N) :=
  ⨅ σ : fixSub N F,
    (fixSub N L).map (MulAut.conj (σ : N ≃ₐ[rationalBase k t] N)).toMonoidHom

variable {F L : IntermediateField (rationalBase k t) Ω}

theorem mem_galoisCore {τ : N ≃ₐ[rationalBase k t] N} :
    τ ∈ galoisCore F L ↔ ∀ σ ∈ fixSub N F, σ⁻¹ * τ * σ ∈ fixSub N L := by
  simp only [galoisCore, Subgroup.mem_iInf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro h σ hσ
    obtain ⟨ρ, hρ, hρτ⟩ := h ⟨σ, hσ⟩
    rw [← hρτ]
    simpa [mul_assoc] using hρ
  · intro h σ
    refine ⟨σ⁻¹ * τ * σ, h σ σ.2, ?_⟩
    simp [mul_assoc]

theorem galoisCore_le : galoisCore (N := N) F L ≤ fixSub N L := by
  intro τ hτ
  simpa using mem_galoisCore.mp hτ 1 (Subgroup.one_mem _)

/-- The relative Galois closure of `L/F` inside the ambient Galois extension `N`. -/
noncomputable def galoisClosure (F L : IntermediateField (rationalBase k t) Ω) :
    IntermediateField (rationalBase k t) Ω :=
  (IntermediateField.fixedField (galoisCore (N := N) F L)).map N.val

theorem galoisClosure_le : galoisClosure (N := N) F L ≤ N := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem le_galoisClosure (hLN : L ≤ N) : L ≤ galoisClosure (N := N) F L := by
  intro y hy
  refine ⟨⟨y, hLN hy⟩, ?_, rfl⟩
  rintro ⟨τ, hτ⟩
  exact galoisCore_le hτ ⟨y, hLN hy⟩ hy

theorem fixSub_galoisClosure [FiniteDimensional (rationalBase k t) N] :
    fixSub N (galoisClosure (N := N) F L) = galoisCore F L := by
  rw [fixSub_eq_fixingSubgroup (galoisClosure_le (F := F) (L := L))]
  have hrestrict :
      IntermediateField.restrict (galoisClosure_le (N := N) (F := F) (L := L)) =
        IntermediateField.fixedField (galoisCore F L) := by
    ext x
    rw [IntermediateField.mem_restrict]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hrestrict, IntermediateField.fixingSubgroup_fixedField]

theorem conj_mem_galoisCore {σ τ : N ≃ₐ[rationalBase k t] N} (hσ : σ ∈ fixSub N F)
    (hτ : τ ∈ galoisCore F L) : σ⁻¹ * τ * σ ∈ galoisCore F L := by
  rw [mem_galoisCore] at hτ ⊢
  intro ρ hρ
  have h := hτ (σ * ρ) ((fixSub N F).mul_mem hσ hρ)
  simpa [mul_assoc] using h

theorem mem_galoisClosure_iff {y : Ω} (hy : y ∈ N) :
    y ∈ galoisClosure (N := N) F L ↔ ∀ τ ∈ galoisCore F L, τ ⟨y, hy⟩ = ⟨y, hy⟩ := by
  constructor
  · rintro ⟨z, hz, hzy⟩ τ hτ
    rw [show (⟨y, hy⟩ : N) = z from Subtype.ext hzy.symm]
    exact (IntermediateField.mem_fixedField_iff _ _).mp hz τ hτ
  · intro h
    exact ⟨⟨y, hy⟩, (IntermediateField.mem_fixedField_iff _ _).mpr h, rfl⟩

theorem apply_mem_galoisClosure {σ : N ≃ₐ[rationalBase k t] N} (hσ : σ ∈ fixSub N F)
    {y : N} (hy : (y : Ω) ∈ galoisClosure (N := N) F L) :
    ((σ y : N) : Ω) ∈ galoisClosure (N := N) F L := by
  rw [mem_galoisClosure_iff (σ y).2]
  rw [mem_galoisClosure_iff y.2] at hy
  change ∀ τ ∈ galoisCore F L, τ (σ y) = σ y
  intro τ hτ
  have h := hy (σ⁻¹ * τ * σ) (conj_mem_galoisCore hσ hτ)
  have hconj : τ (σ y) = σ ((σ⁻¹ * τ * σ) y) := by simp [AlgEquiv.mul_apply]
  rw [hconj, h]

theorem mem_of_forall_fixSub [FiniteDimensional (rationalBase k t) N]
    [IsGalois (rationalBase k t) N] (hFN : F ≤ N) {y : N}
    (hy : ∀ σ ∈ fixSub N F, σ y = y) : (y : Ω) ∈ F := by
  have h : y ∈ IntermediateField.fixedField (fixSub N F) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr hy
  rw [fixSub_eq_fixingSubgroup hFN, IsGalois.fixedField_fixingSubgroup] at h
  exact (IntermediateField.mem_restrict hFN y).mp h

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
