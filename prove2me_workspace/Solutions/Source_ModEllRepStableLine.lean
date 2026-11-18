/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path: Iut/Concrete/ModEllRepGalois.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

universe u

open WeierstrassCurve Matrix
open scoped Classical

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

/-- A stable line gives a Galois-stable cyclic subgroup of order `ℓ`. -/
lemma hasCyclicSubgroup_of_stable_line [Fact ℓ.Prime] (v : Fin 2 → ZMod ℓ) (hv : v ≠ 0)
    (hstab : ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∃ c : ZMod ℓ,
      (R.rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v = c • v) :
    C.HasCyclicSubgroup ℓ := by
  let f : (Fin 2 → ZMod ℓ) →+ Affine.Point (Affine.baseChange C.E C.Fbar) :=
    (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ).subtype.comp
      R.torsionBasis.symm.toAddMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp R.torsionBasis.symm.injective
  have hfσ : ∀ (σ : C.Fbar ≃ₐ[C.F] C.Fbar) (x : Fin 2 → ZMod ℓ),
      galPointMap C.F C.E C.Fbar σ (f x) =
        f ((R.rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ x) := by
    intro σ x
    have h := R.rep_spec σ (R.torsionBasis.symm x)
    rw [AddEquiv.apply_symm_apply] at h
    have h' := congrArg R.torsionBasis.symm h
    rw [AddEquiv.symm_apply_apply] at h'
    exact congrArg Subtype.val h'
  refine ⟨(AddSubgroup.zmultiples v).map f, ?_, ?_⟩
  · rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ f hf).toEquiv, Nat.card_zmultiples,
      addOrderOf_eq_prime (p := ℓ) _ hv]
    ext i
    simp
  · intro σ P hP
    rw [AddSubgroup.mem_map] at hP ⊢
    obtain ⟨x, hx, rfl⟩ := hP
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    obtain ⟨c, hc⟩ := hstab σ
    refine ⟨(n * c.val) • v, AddSubgroup.mem_zmultiples_iff.mpr ⟨n * c.val, rfl⟩, ?_⟩
    have hcv : c • v = (c.val : ℤ) • v := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul, natCast_zsmul]
    rw [hfσ, Matrix.mulVec_smul, hc, hcv, smul_smul]

/-- If there is no cyclic subgroup scheme of order `ℓ`, the image stabilizes no line. -/
lemma exists_mulVec_ne_smul_of_not_hasCyclicSubgroup [Fact ℓ.Prime]
    (h : ¬ C.HasCyclicSubgroup ℓ) (v : Fin 2 → ZMod ℓ) (hv : v ≠ 0) :
    ∃ g ∈ R.rep.range, ∀ c : ZMod ℓ, (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v ≠ c • v := by
  by_contra hcon
  apply h
  refine R.hasCyclicSubgroup_of_stable_line v hv fun σ => ?_
  by_contra hσ
  exact hcon ⟨R.rep σ, ⟨σ, rfl⟩, fun c hc => hσ ⟨c, hc⟩⟩

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData
