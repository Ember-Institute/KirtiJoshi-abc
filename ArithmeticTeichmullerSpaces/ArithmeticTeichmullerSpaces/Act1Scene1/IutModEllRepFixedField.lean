/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/ModEllRepGalois.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapts the fixed-field and Galois-range part of the reference
argument to `IutCurveModEllRepData`. No reference-project import is used.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaModEllRepConstruct
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlacesOver

/-!
source-id: IUT-COR312-MODELLREP-FIXED-FIELD
source: `refer/iut/Iut/Concrete/ModEllRepGalois.lean`.
fidelity: the open kernel of the actual mod-`ell` representation cuts out a
finite Galois torsion field; geometric `ell`-torsion descends to that field,
and the representation range has the same cardinality as its Galois group.
The local Tate and ramification argument is not included here.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCurveModEllRepData

open JoshiTeich.Prologue
open NumberField WeierstrassCurve Matrix
open scoped Classical

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {ell : ℕ} (R : IutCurveModEllRepData F E Fbar ell)

/-! ### The representation fixed field and torsion descent -/

/-- The fixed field cut out by the kernel of the actual representation. -/
noncomputable def torsionField : IntermediateField F Fbar :=
  IntermediateField.fixedField R.rep.ker

local instance (priority := 1100) instDecidableEqTorsionField :
    DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The curve over the representation fixed field. -/
abbrev EK : WeierstrassCurve ↥R.torsionField :=
  E.map (algebraMap F ↥R.torsionField)

/-- Base change of points from the fixed field to the algebraic closure. -/
def bcK : R.EK.toAffine.Point →+ Affine.Point (Affine.baseChange E Fbar) :=
  Affine.Point.map (W' := E) (S := F)
    (IsScalarTower.toAlgHom F ↥R.torsionField Fbar)

lemma bcK_injective : Function.Injective (bcK E Fbar R) :=
  Affine.Point.map_injective (W' := E) (S := F)
    (IsScalarTower.toAlgHom F ↥R.torsionField Fbar)

abbrev TK : AddSubgroup R.EK.toAffine.Point :=
  AddSubgroup.torsionBy R.EK.toAffine.Point ell

abbrev TFbar : AddSubgroup (Affine.Point (Affine.baseChange E Fbar)) :=
  AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell

lemma galPointMap_eq_of_mem_ker {σ : Fbar ≃ₐ[F] Fbar} (hσ : σ ∈ R.rep.ker)
    (Q : ↥(TFbar (E := E) (Fbar := Fbar) (ell := ell))) :
    JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q.1 = Q.1 := by
  have h := R.rep_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (R.torsionBasis.injective h)

lemma exists_bcK_eq (Q : Affine.Point (Affine.baseChange E Fbar))
    (hQ : Q ∈ TFbar (E := E) (Fbar := Fbar) (ell := ell)) :
    ∃ P : R.EK.toAffine.Point, bcK E Fbar R P = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hfix : ∀ σ ∈ R.rep.ker, σ x = x ∧ σ y = y := by
      intro σ hσ
      have h' := galPointMap_eq_of_mem_ker E Fbar R hσ ⟨_, hQ⟩
      simp only [JoshiTeich.ReferenceIut.galPointMap,
        Affine.Point.map_some] at h'
      exact Affine.Point.some.inj h'
    have hx : x ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).1
    have hy : y ∈ R.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).2
    have hns : (Affine.baseChange E ↥R.torsionField).Nonsingular
        (⟨x, hx⟩ : ↥R.torsionField) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := E)
        (IsScalarTower.toAlgHom F ↥R.torsionField Fbar).injective _ _).mp h
    exact ⟨.some _ _ hns, rfl⟩

lemma bcK_mem_TFbar {P : R.EK.toAffine.Point} (hP : P ∈ TK E Fbar R) :
    bcK E Fbar R P ∈ TFbar (E := E) (Fbar := Fbar) (ell := ell) := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

lemma mem_TK_of_bcK {P : R.EK.toAffine.Point}
    (hP : bcK E Fbar R P ∈ TFbar (E := E) (Fbar := Fbar) (ell := ell)) :
    P ∈ TK E Fbar R := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul] at hP
  exact bcK_injective E Fbar R (hP.trans (map_zero _).symm)

def torsionEquiv : ↥(TK E Fbar R) ≃+ ↥(TFbar (E := E) (Fbar := Fbar) (ell := ell)) :=
  AddEquiv.ofBijective
    (((bcK E Fbar R).domRestrict (TK E Fbar R)).codRestrict
      (TFbar (E := E) (Fbar := Fbar) (ell := ell))
      fun P => bcK_mem_TFbar E Fbar R P.2)
    ⟨fun P P' h => Subtype.ext (bcK_injective E Fbar R (congrArg Subtype.val h)),
     fun Q => by
      obtain ⟨P, hP⟩ := exists_bcK_eq E Fbar R Q.1 Q.2
      exact ⟨⟨P, mem_TK_of_bcK E Fbar R (hP ▸ Q.2)⟩, Subtype.ext hP⟩⟩

def basisK : ↥(TK E Fbar R) ≃+ (Fin 2 → ZMod ell) :=
  (torsionEquiv E Fbar R).trans R.torsionBasis

lemma card_torsionBy_EK : Nat.card (TK E Fbar R) = ell ^ 2 := by
  rw [Nat.card_congr (basisK E Fbar R).toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

/-! ### The Galois group of the fixed field -/

instance isGalois_torsionField : IsGalois F ↥R.torsionField :=
  IsGalois.of_fixedField_normal_subgroup R.rep.ker

lemma fixingSubgroup_torsionField :
    R.torsionField.fixingSubgroup = R.rep.ker :=
  InfiniteGalois.fixingSubgroup_fixedField (k := F) (K := Fbar)
    ⟨R.rep.ker, Subgroup.isClosed_of_isOpen _ R.ker_isOpen⟩

lemma restrictNormalHom_ker_eq :
    (AlgEquiv.restrictNormalHom R.torsionField :
      (Fbar ≃ₐ[F] Fbar) →* (↥R.torsionField ≃ₐ[F] ↥R.torsionField)).ker = R.rep.ker := by
  rw [IntermediateField.restrictNormalHom_ker, R.fixingSubgroup_torsionField]

def rangeEquivGal : R.rep.range ≃*
    (↥R.torsionField ≃ₐ[F] ↥R.torsionField) :=
  (QuotientGroup.quotientKerEquivRange R.rep).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq R.restrictNormalHom_ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (AlgEquiv.restrictNormalHom_surjective (F := F)
          (K₁ := ↥R.torsionField) (E := Fbar))))

lemma card_range : Nat.card R.rep.range =
    Nat.card (↥R.torsionField ≃ₐ[F] ↥R.torsionField) :=
  Nat.card_congr R.rangeEquivGal.toEquiv

end

end JoshiTeich.Act1Scene1.IutCurveModEllRepData
