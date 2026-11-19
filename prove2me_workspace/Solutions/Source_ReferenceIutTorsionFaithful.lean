/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/Unramified.lean
-/
import Solutions.Source_ModEllRepGalois

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

open WeierstrassCurve
open scoped Classical

universe u

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

noncomputable local instance (priority := 1100) : DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

private lemma bcK_map_restrictNormalHom (σ : C.Fbar ≃ₐ[C.F] C.Fbar) (P : R.EK.toAffine.Point) :
    R.bcK (Affine.Point.map (W' := C.E) (S := C.F)
      (AlgEquiv.restrictNormalHom R.torsionField σ : ↥R.torsionField →ₐ[C.F] ↥R.torsionField) P) =
      galPointMap C.F C.E C.Fbar σ (R.bcK P) := by
  change (Affine.baseChange C.E ↥R.torsionField).Point at P
  change Affine.Point.map (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)
    (Affine.Point.map (W' := C.E) (S := C.F)
      (AlgEquiv.restrictNormalHom R.torsionField σ : ↥R.torsionField →ₐ[C.F] ↥R.torsionField) P) =
    Affine.Point.map (W' := C.E) (S := C.F) σ.toAlgHom
      (Affine.Point.map (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar) P)
  rw [Affine.Point.map_map, Affine.Point.map_map]
  have h : (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar).comp
      (AlgEquiv.restrictNormalHom R.torsionField σ : ↥R.torsionField →ₐ[C.F] ↥R.torsionField) =
      σ.toAlgHom.comp (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar) := by
    ext a
    exact AlgEquiv.restrictNormalHom_apply R.torsionField σ a
  rw [h]

/-- Every automorphism of the torsion field that fixes all the torsion points is the identity. -/
theorem eq_one_of_forall_torsion (σ : ↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)
    (h : ∀ P : R.EK.toAffine.Point, ℓ • P = 0 →
      Affine.Point.map (W' := C.E) (S := C.F) σ.toAlgHom P = P) : σ = 1 := by
  obtain ⟨τ, rfl⟩ :=
    (AlgEquiv.restrictNormalHom_surjective (F := C.F) (K₁ := ↥R.torsionField) C.Fbar) σ
  have hfix : ∀ Q : ↥(TFbar C ℓ), galPointMap C.F C.E C.Fbar τ Q.1 = Q.1 := by
    intro Q
    obtain ⟨P, hP⟩ := R.exists_bcK_eq Q.1 Q.2
    have hPT : ℓ • P = 0 :=
      AddSubgroup.torsionBy.nsmul_iff.mp (R.mem_TK_of_bcK (hP ▸ Q.2))
    rw [← hP, ← R.bcK_map_restrictNormalHom, h P hPT]
  have hrep : R.rep τ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨Q, rfl⟩ := R.torsionBasis.surjective v
    rw [Matrix.toLin'_apply, ← R.rep_spec τ Q, Matrix.toLin'_one, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (hfix Q)
  have hτ : τ ∈ (AlgEquiv.restrictNormalHom R.torsionField).ker := by
    rw [R.restrictNormalHom_ker_eq]
    exact MonoidHom.mem_ker.mpr hrep
  exact MonoidHom.mem_ker.mp hτ

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData
