/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutWeierstrassLocalization
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
source-id: IUT-COR312-TORSION-RATIONALITY
source: `iut`: `refer/iut/Iut/Anabelian/Torsion.lean` and
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`.
fidelity: ports the fixed-field rationality argument for elliptic-curve `ell`-torsion
from the chosen algebraic-closure basis and its genuine Galois representation. The
representation data are explicit inputs; openness of its kernel and the remaining
admissible-prime fields are not constructed here.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve
open scoped Classical

universe uF uFbar

noncomputable section

variable {F : Type uF} [Field F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type uFbar} [Field Fbar] [Algebra F Fbar]

/-- The action on affine points induced by an automorphism over the base field. -/
def iutGaloisPointMap (σ : Fbar ≃ₐ[F] Fbar) :
    Affine.Point (Affine.baseChange E Fbar) →+ Affine.Point (Affine.baseChange E Fbar) :=
  Affine.Point.map (W' := E) σ.toAlgHom

omit [E.IsElliptic] in
lemma iutGaloisPointMap_torsionBy {ell : ℕ} (σ : Fbar ≃ₐ[F] Fbar)
    {P : Affine.Point (Affine.baseChange E Fbar)}
    (hP : P ∈ AddSubgroup.torsionBy
      (Affine.Point (Affine.baseChange E Fbar)) ell) :
    iutGaloisPointMap (E := E) (Fbar := Fbar) σ P ∈
      AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

/-- The torsion-basis and representation fields used from IUT's admissible-prime data. -/
structure IutTorsionRepresentationData (ell : ℕ) where
  closure : IsAlgClosure F Fbar
  basisOverClosure :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell)
  representation : (Fbar ≃ₐ[F] Fbar) →*
    Matrix.GeneralLinearGroup (Fin 2) (ZMod ell)
  representation_spec : ∀ (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell),
    basisOverClosure
        ⟨iutGaloisPointMap (E := E) (Fbar := Fbar) σ P.1,
          iutGaloisPointMap_torsionBy (E := E) (Fbar := Fbar) σ P.2⟩ =
      (representation σ : Matrix (Fin 2) (Fin 2) (ZMod ell)).mulVec
        (basisOverClosure P)

namespace IutTorsionRepresentationData

variable {ell : ℕ} (D : IutTorsionRepresentationData (F := F) (E := E)
  (Fbar := Fbar) ell)

/-- The field fixed by the kernel of the mod-`ell` representation. -/
noncomputable def torsionField : IntermediateField F Fbar :=
  IntermediateField.fixedField D.representation.ker

omit [E.IsElliptic] in
/-- The fixed field of the representation kernel is Galois over the base field. -/
theorem isGalois_torsionField [NumberField F] : IsGalois F ↥D.torsionField := by
  letI : IsAlgClosure F Fbar := D.closure
  exact IsGalois.of_fixedField_normal_subgroup D.representation.ker

omit [E.IsElliptic] in
/-- The genuine action on an algebraic torsion basis makes the representation kernel open. -/
theorem representation_ker_isOpen :
    IsOpen (D.representation.ker : Set (Fbar ≃ₐ[F] Fbar)) := by
  letI : IsAlgClosure F Fbar := D.closure
  let basisPoint (j : Fin 2) := D.basisOverClosure.symm (Pi.single j (1 : ZMod ell))
  let xCoordinate : Affine.Point (Affine.baseChange E Fbar) → Fbar
    | .zero => 0
    | .some x _ _ => x
  let yCoordinate : Affine.Point (Affine.baseChange E Fbar) → Fbar
    | .zero => 0
    | .some _ y _ => y
  let S : Set Fbar := Set.range fun ij : Fin 2 × Fin 2 =>
    if ij.2 = 0 then xCoordinate (basisPoint ij.1).1 else yCoordinate (basisPoint ij.1).1
  let K := IntermediateField.adjoin F S
  have hSIntegral : ∀ x ∈ S, IsIntegral F x := by
    intro x hx
    rcases Set.mem_range.mp hx with ⟨ij, rfl⟩
    exact (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hKFinite : FiniteDimensional F K := IntermediateField.finiteDimensional_adjoin hSIntegral
  letI : FiniteDimensional F K := hKFinite
  have hKOpen : IsOpen (K.fixingSubgroup : Set (Fbar ≃ₐ[F] Fbar)) :=
    IntermediateField.fixingSubgroup_isOpen K
  have hfixing_le_kernel : K.fixingSubgroup ≤ D.representation.ker := by
    intro σ hσ
    change D.representation σ = 1
    apply Units.ext
    apply Matrix.ext
    intro i j
    let v : Fin 2 → ZMod ell := Pi.single j 1
    let P := D.basisOverClosure.symm v
    have hpoint : iutGaloisPointMap (E := E) (Fbar := Fbar) σ P.1 = P.1 := by
      cases hP : P.1 with
      | zero => exact Affine.Point.map_zero _
      | some x y hn =>
        have hxS : x ∈ S := by
          apply Set.mem_range.mpr
          refine ⟨(j, 0), ?_⟩
          simp [xCoordinate, basisPoint, P, v, hP]
        have hyS : y ∈ S := by
          apply Set.mem_range.mpr
          refine ⟨(j, 1), ?_⟩
          simp [yCoordinate, basisPoint, P, v, hP]
        have hxK : x ∈ K := IntermediateField.subset_adjoin _ _ hxS
        have hyK : y ∈ K := IntermediateField.subset_adjoin _ _ hyS
        have hxfix : σ x = x :=
          (IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ x hxK
        have hyfix : σ y = y :=
          (IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ y hyK
        rw [iutGaloisPointMap, Affine.Point.map_some]
        simp [hxfix, hyfix]
    have hPfixed :
        (⟨iutGaloisPointMap (E := E) (Fbar := Fbar) σ P.1,
          iutGaloisPointMap_torsionBy (E := E) (Fbar := Fbar) σ P.2⟩ :
            AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) =
          P := Subtype.ext hpoint
    have hspec := D.representation_spec σ P
    rw [hPfixed] at hspec
    have hv : v = (D.representation σ : Matrix (Fin 2) (Fin 2) (ZMod ell)).mulVec v := by
      simpa [P, v] using hspec
    have hentry :
        (D.representation σ : Matrix (Fin 2) (Fin 2) (ZMod ell)) i j = v i := by
      simpa [v, Matrix.mulVec_single_one, Matrix.col_apply] using (congrFun hv i).symm
    fin_cases i <;> fin_cases j <;>
      simpa [v, Matrix.one_apply] using hentry
  exact Subgroup.isOpen_mono hfixing_le_kernel hKOpen

omit [E.IsElliptic] in
/-- The fixed field of the genuine torsion representation has finite dimension over the base. -/
theorem finiteDimensional_torsionField [NumberField F] :
    FiniteDimensional F ↥D.torsionField := by
  letI : IsAlgClosure F Fbar := D.closure
  have hle : D.representation.ker ≤ D.torsionField.fixingSubgroup :=
    (IntermediateField.le_iff_le D.representation.ker D.torsionField).mp le_rfl
  have hopen : IsOpen (D.torsionField.fixingSubgroup : Set (Fbar ≃ₐ[F] Fbar)) :=
    Subgroup.isOpen_mono hle D.representation_ker_isOpen
  exact (InfiniteGalois.isOpen_iff_finite D.torsionField).mp hopen

omit [E.IsElliptic] in
/-- The fixed field of the genuine torsion representation is itself a number field. -/
theorem numberField_torsionField [NumberField F] :
    NumberField ↥D.torsionField := by
  letI : IsAlgClosure F Fbar := D.closure
  have : FiniteDimensional F ↥D.torsionField := D.finiteDimensional_torsionField
  have : CharZero ↥D.torsionField :=
    charZero_of_injective_algebraMap (algebraMap F ↥D.torsionField).injective
  have : IsScalarTower ℚ F ↥D.torsionField :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : FiniteDimensional ℚ ↥D.torsionField := Module.Finite.trans F ↥D.torsionField
  exact { }

local instance (priority := high) instDecidableEqTorsionField :
    DecidableEq ↥D.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The original elliptic curve over the fixed field. -/
abbrev curveOverTorsionField : WeierstrassCurve ↥D.torsionField :=
  E.map (algebraMap F ↥D.torsionField)

/-- Base change from the fixed field to the coefficient field. -/
def baseChangeToClosure : D.curveOverTorsionField.toAffine.Point →+
    Affine.Point (Affine.baseChange E Fbar) :=
  Affine.Point.map (W' := E) (S := F)
    (IsScalarTower.toAlgHom F ↥D.torsionField Fbar)

omit [E.IsElliptic] in
lemma baseChangeToClosure_injective : Function.Injective D.baseChangeToClosure :=
  Affine.Point.map_injective (W' := E) (S := F)
    (IsScalarTower.toAlgHom F ↥D.torsionField Fbar)

/-- The `ell`-torsion over the fixed field. -/
abbrev torsionOverTorsionField : AddSubgroup D.curveOverTorsionField.toAffine.Point :=
  AddSubgroup.torsionBy D.curveOverTorsionField.toAffine.Point ell

/-- The `ell`-torsion over the coefficient field. -/
abbrev torsionOverClosure
    (_D : IutTorsionRepresentationData (F := F) (E := E) (Fbar := Fbar) ell) :
    AddSubgroup (Affine.Point (Affine.baseChange E Fbar)) :=
  AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell

omit [E.IsElliptic] in
/-- Kernel elements fix all `ell`-torsion points by the representation characterizing law. -/
lemma galoisPoint_eq_of_mem_kernel {σ : Fbar ≃ₐ[F] Fbar}
    (hσ : σ ∈ D.representation.ker) (Q : ↥D.torsionOverClosure) :
    iutGaloisPointMap (E := E) (Fbar := Fbar) σ Q.1 = Q.1 := by
  have h := D.representation_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (D.basisOverClosure.injective h)

omit [E.IsElliptic] in
/-- Every `ell`-torsion point over the closure descends to the representation fixed field. -/
lemma exists_baseChangeToClosure_eq
    (Q : Affine.Point (Affine.baseChange E Fbar)) (hQ : Q ∈ D.torsionOverClosure) :
    ∃ R : D.curveOverTorsionField.toAffine.Point, D.baseChangeToClosure R = Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hfix : ∀ σ ∈ D.representation.ker, σ x = x ∧ σ y = y := by
      intro σ hσ
      have h' := D.galoisPoint_eq_of_mem_kernel hσ ⟨_, hQ⟩
      simp only [iutGaloisPointMap] at h'
      exact Affine.Point.some.inj h'
    have hx : x ∈ D.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).1
    have hy : y ∈ D.torsionField := by
      rw [torsionField, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => (hfix σ hσ).2
    have hns : (Affine.baseChange E ↥D.torsionField).Nonsingular
        (⟨x, hx⟩ : ↥D.torsionField) ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular (W := E)
        (IsScalarTower.toAlgHom F ↥D.torsionField Fbar).injective _ _).mp h
    exact ⟨.some _ _ hns, rfl⟩

omit [E.IsElliptic] in
lemma baseChangeToClosure_mem_torsion
    {R : D.curveOverTorsionField.toAffine.Point}
    (hR : R ∈ D.torsionOverTorsionField) :
    D.baseChangeToClosure R ∈ D.torsionOverClosure := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul, hR, map_zero]

omit [E.IsElliptic] in
lemma mem_torsionOverTorsionField_of_baseChange
    {R : D.curveOverTorsionField.toAffine.Point}
    (hR : D.baseChangeToClosure R ∈ D.torsionOverClosure) :
    R ∈ D.torsionOverTorsionField := by
  rw [AddSubgroup.torsionBy.nsmul_iff] at hR ⊢
  rw [← map_nsmul] at hR
  exact D.baseChangeToClosure_injective (hR.trans (map_zero _).symm)

/-- Base change identifies torsion over the fixed field with torsion over the closure. -/
def torsionEquiv : ↥D.torsionOverTorsionField ≃+ ↥D.torsionOverClosure :=
  AddEquiv.ofBijective
    (D.baseChangeToClosure.domRestrict D.torsionOverTorsionField |>.codRestrict _
      fun R => D.baseChangeToClosure_mem_torsion R.2)
    ⟨fun R R' h => Subtype.ext
        (D.baseChangeToClosure_injective (congrArg Subtype.val h)),
      fun Q => by
        obtain ⟨R, hR⟩ := D.exists_baseChangeToClosure_eq Q.1 Q.2
        exact ⟨⟨R, D.mem_torsionOverTorsionField_of_baseChange (hR ▸ Q.2)⟩,
          Subtype.ext hR⟩⟩

/-- The chosen basis descends to torsion over the representation fixed field. -/
def basisOverTorsionField :
    ↥D.torsionOverTorsionField ≃+ (Fin 2 → ZMod ell) :=
  D.torsionEquiv.trans D.basisOverClosure

omit [E.IsElliptic] in
lemma card_torsionOverTorsionField :
    Nat.card D.torsionOverTorsionField = ell ^ 2 := by
  rw [Nat.card_congr D.basisOverTorsionField.toEquiv, Nat.card_pi, Nat.card_zmod]
  simp

/-- Package the descended basis in the global torsion interface consumed by S1.95. -/
def toGlobalTorsionBasis :
    IutGlobalTorsionBasis D.curveOverTorsionField.toAffine.Point ell where
  torsion := D.torsionOverTorsionField
  torsion_le := le_rfl
  basis := D.basisOverTorsionField

end IutTorsionRepresentationData

end

end JoshiTeich.Act1Scene1
