/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/ModEllRepGalois.lean
-/
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData

open WeierstrassCurve Matrix
open scoped Classical

universe u

noncomputable section

variable {C : EllipticCurveData.{u}} {ℓ : ℕ} (R : C.ModEllRepData ℓ)

local instance (priority := 1100) instDecidableEqTorsionField : DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The curve over the torsion field `K`. -/
abbrev EK : WeierstrassCurve ↥R.torsionField :=
  C.E.map (algebraMap C.F ↥R.torsionField)

/-- Base change of points from `K` to the chosen algebraic closure. -/
def bcK : R.EK.toAffine.Point →+ Affine.Point (Affine.baseChange C.E C.Fbar) :=
  Affine.Point.map (W' := C.E) (S := C.F)
    (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

lemma bcK_injective : Function.Injective R.bcK :=
  Affine.Point.map_injective (W' := C.E) (S := C.F)
    (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar)

/-- The `ℓ`-torsion over `K`. -/
abbrev TK : AddSubgroup R.EK.toAffine.Point := AddSubgroup.torsionBy R.EK.toAffine.Point ℓ

/-- The `ℓ`-torsion over the chosen algebraic closure. -/
abbrev TFbar (C : EllipticCurveData.{u}) (ℓ : ℕ) :
    AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)) :=
  AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ

lemma galPointMap_eq_of_mem_ker {σ : C.Fbar ≃ₐ[C.F] C.Fbar} (hσ : σ ∈ R.rep.ker)
    (Q : ↥(TFbar C ℓ)) : galPointMap C.F C.E C.Fbar σ Q.1 = Q.1 := by
  have h := R.rep_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (R.torsionBasis.injective h)

/-- Every geometric `ℓ`-torsion point comes from a point over `K`. -/
lemma exists_bcK_eq (Q : Affine.Point (Affine.baseChange C.E C.Fbar))
    (hQ : Q ∈ TFbar C ℓ) : ∃ P : R.EK.toAffine.Point, R.bcK P = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hfix : ∀ σ ∈ R.rep.ker, σ x = x ∧ σ y = y := by
      intro σ hσ
      have h' := R.galPointMap_eq_of_mem_ker hσ ⟨_, hQ⟩
      simp only [galPointMap, Affine.Point.map_some] at h'
      exact Affine.Point.some.inj h'
    have hx : x ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).1
    have hy : y ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).2
    have hns : (Affine.baseChange C.E ↥R.torsionField).Nonsingular
        (⟨x, hx⟩ : ↥R.torsionField) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := C.E)
        (IsScalarTower.toAlgHom C.F ↥R.torsionField C.Fbar).injective _ _).mp h
    exact ⟨.some _ _ hns, rfl⟩

lemma bcK_mem_TFbar {P : R.EK.toAffine.Point} (hP : P ∈ R.TK) : R.bcK P ∈ TFbar C ℓ := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

lemma mem_TK_of_bcK {P : R.EK.toAffine.Point} (hP : R.bcK P ∈ TFbar C ℓ) : P ∈ R.TK := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul] at hP
  exact R.bcK_injective (hP.trans (map_zero _).symm)

/-- Base change induces an additive equivalence on the `ℓ`-torsion. -/
def torsionEquiv : ↥R.TK ≃+ ↥(TFbar C ℓ) :=
  AddEquiv.ofBijective
    ((R.bcK.domRestrict R.TK).codRestrict (TFbar C ℓ) fun P => R.bcK_mem_TFbar P.2)
    ⟨fun P P' h => Subtype.ext (R.bcK_injective (congrArg Subtype.val h)),
     fun Q => by
      obtain ⟨P, hP⟩ := R.exists_bcK_eq Q.1 Q.2
      exact ⟨⟨P, R.mem_TK_of_bcK (hP ▸ Q.2)⟩, Subtype.ext hP⟩⟩

/-- The `ℓ`-torsion over `K` has cardinality `ℓ ^ 2`. -/
lemma card_torsionBy_EK : Nat.card R.TK = ℓ ^ 2 := by
  rw [Nat.card_congr (R.torsionEquiv.trans R.torsionBasis).toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

/-- The fixed field of the normal subgroup `ker ρ` is Galois over `F`. -/
instance isGalois_torsionField : IsGalois C.F ↥R.torsionField :=
  IsGalois.of_fixedField_normal_subgroup R.rep.ker

lemma fixingSubgroup_torsionField : R.torsionField.fixingSubgroup = R.rep.ker :=
  InfiniteGalois.fixingSubgroup_fixedField (k := C.F) (K := C.Fbar)
    ⟨R.rep.ker, Subgroup.isClosed_of_isOpen _ R.ker_isOpen⟩

lemma restrictNormalHom_ker_eq :
    (AlgEquiv.restrictNormalHom R.torsionField :
      (C.Fbar ≃ₐ[C.F] C.Fbar) →* (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField)).ker = R.rep.ker := by
  rw [IntermediateField.restrictNormalHom_ker, R.fixingSubgroup_torsionField]

/-- The representation image and the Galois group of `K/F` are both quotients by `ker ρ`. -/
def rangeEquivGal : R.rep.range ≃* (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) :=
  (QuotientGroup.quotientKerEquivRange R.rep).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq R.restrictNormalHom_ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (AlgEquiv.restrictNormalHom_surjective (F := C.F) (K₁ := ↥R.torsionField)
          (E := C.Fbar))))

lemma card_range : Nat.card R.rep.range = Nat.card (↥R.torsionField ≃ₐ[C.F] ↥R.torsionField) :=
  Nat.card_congr R.rangeEquivGal.toEquiv

end

end AbcAdaptation.Reference.Iut.EllipticCurveData.ModEllRepData
