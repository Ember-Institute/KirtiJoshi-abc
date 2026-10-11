/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/CyclicSubgroup.lean` and
`refer/iut/Iut/Concrete/ModEllRepGalois.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapts the stable-line and cyclic-subgroup argument to the local
`IutCurveModEllRepData` contract. No reference-project import is used.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaModEllRepConstruct

/-!
source-id: IUT-COR312-MODELLREP-CYCLIC-SUBGROUP
source: `refer/iut/Iut/Concrete/CyclicSubgroup.lean` and
`refer/iut/Iut/Concrete/ModEllRepGalois.lean`.
fidelity: a stable line for the actual Galois action in a chosen torsion basis
produces a Galois-stable subgroup of order `ell`; conversely, absence of this
cyclic subgroup gives the non-stable-line witness needed by the independent
`IutSL2` generation theorem. The fixed-field and local Tate arguments remain
separate source obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField WeierstrassCurve Matrix
open scoped Classical

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

/-- A Galois-stable subgroup of the geometric `ell`-torsion of order `ell`.

This is the local form of the cyclic subgroup scheme obstruction used by the
mod-`ell` image argument. It is kept in Scene1 because it is tied to the
chosen geometric curve and representation data.
-/
def IutHasCyclicSubgroup (ell : ℕ) : Prop :=
  ∃ H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar)),
    Nat.card H = ell ∧
      ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ P ∈ H,
        JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P ∈ H

variable {E Fbar}

lemma iut_nsmul_eq_zero_of_mem_of_card_eq {ell : ℕ}
    {H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))}
    (hH : Nat.card H = ell)
    {P : Affine.Point (Affine.baseChange E Fbar)} (hP : P ∈ H) :
    ell • P = 0 := by
  have h := card_nsmul_eq_zero' (x := (⟨P, hP⟩ : H))
  rw [hH] at h
  exact congrArg Subtype.val h

lemma iut_le_torsionBy_of_card_eq {ell : ℕ}
    {H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))}
    (hH : Nat.card H = ell) :
    H ≤ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell :=
  fun _ hP => AddSubgroup.torsionBy.nsmul_iff.mpr
    (iut_nsmul_eq_zero_of_mem_of_card_eq hH hP)

lemma IutHasCyclicSubgroup.exists_le_torsionBy {ell : ℕ}
    (h : IutHasCyclicSubgroup E Fbar ell) :
    ∃ H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar)),
      Nat.card H = ell ∧
      (∀ σ : Fbar ≃ₐ[F] Fbar, ∀ P ∈ H,
        JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P ∈ H) ∧
      H ≤ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell := by
  obtain ⟨H, hH, hgal⟩ := h
  exact ⟨H, hH, hgal, iut_le_torsionBy_of_card_eq hH⟩

namespace IutCurveModEllRepData

variable {ell : ℕ} (R : IutCurveModEllRepData F E Fbar ell)

lemma hasCyclicSubgroup_of_stable_line [Fact ell.Prime]
    (v : Fin 2 → ZMod ell) (hv : v ≠ 0)
    (hstab : ∀ σ : Fbar ≃ₐ[F] Fbar, ∃ c : ZMod ell,
      (R.rep σ : Matrix (Fin 2) (Fin 2) (ZMod ell)) *ᵥ v = c • v) :
    IutHasCyclicSubgroup E Fbar ell := by
  let f : (Fin 2 → ZMod ell) →+ Affine.Point (Affine.baseChange E Fbar) :=
    (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell).subtype.comp
      R.torsionBasis.symm.toAddMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp R.torsionBasis.symm.injective
  have hfσ : ∀ (σ : Fbar ≃ₐ[F] Fbar) (x : Fin 2 → ZMod ell),
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ (f x) =
        f ((R.rep σ : Matrix (Fin 2) (Fin 2) (ZMod ell)) *ᵥ x) := by
    intro σ x
    have h := R.rep_spec σ (R.torsionBasis.symm x)
    rw [AddEquiv.apply_symm_apply] at h
    have h' := congrArg R.torsionBasis.symm h
    rw [AddEquiv.symm_apply_apply] at h'
    exact congrArg Subtype.val h'
  refine ⟨(AddSubgroup.zmultiples v).map f, ?_, ?_⟩
  · rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ f hf).toEquiv,
      Nat.card_zmultiples, addOrderOf_eq_prime (p := ell) _ hv]
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

lemma exists_mulVec_ne_smul_of_not_hasCyclicSubgroup [Fact ell.Prime]
    (h : ¬ IutHasCyclicSubgroup E Fbar ell) (v : Fin 2 → ZMod ell) (hv : v ≠ 0) :
    ∃ g ∈ R.rep.range, ∀ c : ZMod ell,
      (g : Matrix (Fin 2) (Fin 2) (ZMod ell)) *ᵥ v ≠ c • v := by
  by_contra hcon
  apply h
  refine R.hasCyclicSubgroup_of_stable_line v hv fun σ => ?_
  by_contra hσ
  exact hcon ⟨R.rep σ, ⟨σ, rfl⟩, fun c hc => hσ ⟨c, hc⟩⟩

end IutCurveModEllRepData

end

end JoshiTeich.Act1Scene1
