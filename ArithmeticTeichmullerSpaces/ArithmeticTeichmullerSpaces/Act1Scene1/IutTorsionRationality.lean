/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutWeierstrassLocalization
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.AdmissiblePrime
import Mathlib.Algebra.Module.ZMod
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
from the chosen algebraic-closure basis and the genuine Galois action. The matrix
representation and its characterizing law are derived from the basis. The basis remains an
explicit input; kernel openness and fixed-field consequences are proved below. A narrow
admissible-prime projection now derives the torsion field, its basis, and the q-root
construction's prime consequences without claiming to construct the remaining source data.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve
open NumberField
open scoped Classical

universe uF uFbar
universe u

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

/-- The genuine Galois action on the `ell`-torsion points is an additive equivalence. -/
def iutGaloisTorsionEquiv {ell : ℕ} (σ : Fbar ≃ₐ[F] Fbar) :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell where
  toFun P := ⟨iutGaloisPointMap (E := E) (Fbar := Fbar) σ P.1,
    iutGaloisPointMap_torsionBy (E := E) (Fbar := Fbar) σ P.2⟩
  invFun P := ⟨iutGaloisPointMap (E := E) (Fbar := Fbar) σ.symm P.1,
    iutGaloisPointMap_torsionBy (E := E) (Fbar := Fbar) σ.symm P.2⟩
  left_inv P := by
    apply Subtype.ext
    simp only [iutGaloisPointMap, Affine.Point.map_map]
    have hcomp : σ.symm.toAlgHom.comp σ.toAlgHom = AlgHom.id F Fbar := by
      ext x
      simp
    rw [hcomp]
    cases P.1 <;> rfl
  right_inv P := by
    apply Subtype.ext
    simp only [iutGaloisPointMap, Affine.Point.map_map]
    have hcomp : σ.toAlgHom.comp σ.symm.toAlgHom = AlgHom.id F Fbar := by
      ext x
      simp
    rw [hcomp]
    cases P.1 <;> rfl
  map_add' P Q := by
    apply Subtype.ext
    exact map_add (iutGaloisPointMap (E := E) (Fbar := Fbar) σ) P.1 Q.1

omit [E.IsElliptic] in
/-- Galois automorphisms act on the additive group of `ell`-torsion points. -/
lemma iutGaloisPointMap_one (P : Affine.Point (Affine.baseChange E Fbar)) :
    iutGaloisPointMap (E := E) (Fbar := Fbar) (1 : Fbar ≃ₐ[F] Fbar) P = P := by
  cases P <;> rfl

omit [E.IsElliptic] in
lemma iutGaloisPointMap_mul (σ τ : Fbar ≃ₐ[F] Fbar)
    (P : Affine.Point (Affine.baseChange E Fbar)) :
    iutGaloisPointMap (E := E) (Fbar := Fbar) σ
        (iutGaloisPointMap (E := E) (Fbar := Fbar) τ P) =
      iutGaloisPointMap (E := E) (Fbar := Fbar) (σ * τ) P := by
  simp only [iutGaloisPointMap, Affine.Point.map_map]
  have hcomp : σ.toAlgHom.comp τ.toAlgHom = (σ * τ).toAlgHom := by
    ext x
    simp [AlgEquiv.mul_apply]
  rw [hcomp]

local instance iutTorsionByZModModule {ell : ℕ} :
    Module (ZMod ell)
      (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) :=
  AddSubgroup.torsionBy.zmodModule

/-- The genuine Galois action on torsion points is linear over `ZMod ell`. -/
noncomputable def iutGaloisTorsionLinearAction {ell : ℕ} :
    (Fbar ≃ₐ[F] Fbar) →*
      (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃ₗ[ZMod ell]
        AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) := by
  let T := AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell
  letI : SMul (Fbar ≃ₐ[F] Fbar) T := ⟨fun σ P => iutGaloisTorsionEquiv σ P⟩
  letI : MulAction (Fbar ≃ₐ[F] Fbar) T := {
    smul := fun σ P => iutGaloisTorsionEquiv σ P
    one_smul P := by
      apply Subtype.ext
      exact iutGaloisPointMap_one (E := E) (Fbar := Fbar) P.1
    mul_smul σ τ P := by
      apply Subtype.ext
      exact (iutGaloisPointMap_mul (E := E) (Fbar := Fbar) σ τ P.1).symm
  }
  letI : DistribMulAction (Fbar ≃ₐ[F] Fbar) T := {
    __ := (inferInstance : MulAction (Fbar ≃ₐ[F] Fbar) T)
    smul_zero σ := by
      apply Subtype.ext
      exact map_zero (iutGaloisPointMap (E := E) (Fbar := Fbar) σ)
    smul_add σ P Q := by
      apply Subtype.ext
      exact map_add (iutGaloisPointMap (E := E) (Fbar := Fbar) σ) P.1 Q.1
  }
  letI : SMulCommClass (Fbar ≃ₐ[F] Fbar) (ZMod ell) T := {
    smul_comm σ c P := ZMod.map_smul (iutGaloisTorsionEquiv σ) c P
  }
  exact DistribMulAction.toModuleAut (ZMod ell) T

/-- View an additive torsion basis as a `ZMod ell`-linear equivalence. -/
def iutTorsionBasisLinearEquiv {ell : ℕ}
    (basis : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell)) :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃ₗ[ZMod ell]
      (Fin 2 → ZMod ell) :=
  basis.toLinearEquiv (fun c x => ZMod.map_smul basis c x)

/-- The canonical mod-`ell` matrix representation of the genuine Galois action in a chosen
rank-two torsion basis. -/
noncomputable def iutTorsionRepresentationOfBasis {ell : ℕ}
    (basis : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell)) :
    (Fbar ≃ₐ[F] Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ell) := by
  let T := AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell
  let basisLinear := iutTorsionBasisLinearEquiv (E := E) (Fbar := Fbar) basis
  let torsionLinearAut : (Fbar ≃ₐ[F] Fbar) →*
      LinearMap.GeneralLinearGroup (ZMod ell) T :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod ell) T).symm.toMonoidHom.comp
      (iutGaloisTorsionLinearAction (E := E) (Fbar := Fbar) (ell := ell))
  let coordinateLinearAut : (Fbar ≃ₐ[F] Fbar) →*
      LinearMap.GeneralLinearGroup (ZMod ell) (Fin 2 → ZMod ell) :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv basisLinear).toMonoidHom.comp
      torsionLinearAut
  exact (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod ell) (Fin 2))).symm.toMonoidHom.comp
    coordinateLinearAut

/-- The algebraic closure and torsion basis used from IUT's admissible-prime data. -/
structure IutTorsionRepresentationData (ell : ℕ) where
  closure : IsAlgClosure F Fbar
  basisOverClosure :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell)

omit [E.IsElliptic] in
theorem iutTorsionRepresentationOfBasis_spec {ell : ℕ}
    (basis : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell)) (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) :
    basis ⟨iutGaloisPointMap (E := E) (Fbar := Fbar) σ P.1,
      iutGaloisPointMap_torsionBy (E := E) (Fbar := Fbar) σ P.2⟩ =
        (iutTorsionRepresentationOfBasis (E := E) (Fbar := Fbar) basis σ :
          Matrix (Fin 2) (Fin 2) (ZMod ell)).mulVec (basis P) := by
  let T := AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell
  let bL := iutTorsionBasisLinearEquiv (E := E) (Fbar := Fbar) basis
  have hMatrix :
      Matrix.GeneralLinearGroup.toLin' (Pi.basisFun (ZMod ell) (Fin 2))
          (iutTorsionRepresentationOfBasis (E := E) (Fbar := Fbar) basis σ) =
        LinearMap.GeneralLinearGroup.congrLinearEquiv bL
          ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod ell) T).symm
            (iutGaloisTorsionLinearAction (E := E) (Fbar := Fbar) σ)) := by
    simp [iutTorsionRepresentationOfBasis, bL, T]
  have hAction :
      iutGaloisTorsionLinearAction (E := E) (Fbar := Fbar) σ P =
        ⟨iutGaloisPointMap (E := E) (Fbar := Fbar) σ P.1,
          iutGaloisPointMap_torsionBy (E := E) (Fbar := Fbar) σ P.2⟩ := rfl
  have hEval := congrArg
    (fun A : LinearMap.GeneralLinearGroup (ZMod ell) (Fin 2 → ZMod ell) =>
      A.toLinearEquiv (basis P)) hMatrix
  ext i
  have hEvalAt := congrArg (fun v : Fin 2 → ZMod ell => v i) hEval
  have hrepr : (Pi.basisFun (ZMod ell) (Fin 2)).repr (basis P) = basis P := by
    ext j
    simp
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at hEvalAt
  rw [hrepr] at hEvalAt
  simp only [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
    LinearMap.GeneralLinearGroup.generalLinearEquiv] at hEvalAt
  simp [LinearMap.GeneralLinearGroup.toLinearEquiv,
    LinearMap.GeneralLinearGroup.ofLinearEquiv, LinearEquiv.trans_apply,
    bL, iutTorsionBasisLinearEquiv] at hEvalAt
  change _ = basis (iutGaloisTorsionLinearAction (E := E) (Fbar := Fbar) σ P) i at hEvalAt
  rw [hAction] at hEvalAt
  fin_cases i <;>
    simpa [Pi.basisFun_apply, Pi.single_apply, Fintype.linearCombination_apply] using hEvalAt.symm

namespace IutTorsionRepresentationData

variable {ell : ℕ} (D : IutTorsionRepresentationData (F := F) (E := E)
  (Fbar := Fbar) ell)

/-- The matrix representation derived from the genuine Galois action in the chosen basis. -/
noncomputable def representation : (Fbar ≃ₐ[F] Fbar) →*
    Matrix.GeneralLinearGroup (Fin 2) (ZMod ell) :=
  iutTorsionRepresentationOfBasis (E := E) (Fbar := Fbar) D.basisOverClosure

omit [E.IsElliptic] in
/-- The derived matrix representation records the genuine action on every torsion point. -/
theorem representation_spec (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) :
    D.basisOverClosure
        ⟨iutGaloisPointMap (E := E) (Fbar := Fbar) σ P.1,
          iutGaloisPointMap_torsionBy (E := E) (Fbar := Fbar) σ P.2⟩ =
      (D.representation σ : Matrix (Fin 2) (Fin 2) (ZMod ell)).mulVec
        (D.basisOverClosure P) :=
  iutTorsionRepresentationOfBasis_spec (E := E) (Fbar := Fbar)
    D.basisOverClosure σ P

/-- Construct the genuine mod-`ell` representation from the closure torsion basis and
the functorial Galois action on Weierstrass points. -/
noncomputable def ofBasis {ell : ℕ} (closure : IsAlgClosure F Fbar)
    (basis : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell)) :
    IutTorsionRepresentationData (F := F) (E := E) (Fbar := Fbar) ell where
  closure := closure
  basisOverClosure := basis

/-- The field fixed by the kernel of the mod-`ell` representation. -/
noncomputable def torsionField : IntermediateField F Fbar :=
  IntermediateField.fixedField D.representation.ker

omit [E.IsElliptic] in
omit [E.IsElliptic] in
/-- The fixed field of the representation kernel is Galois over the base field. -/
theorem isGalois_torsionField [NumberField F] : IsGalois F ↥D.torsionField := by
  letI : IsAlgClosure F Fbar := D.closure
  exact IsGalois.of_fixedField_normal_subgroup D.representation.ker

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

/-- The fixed field of the genuine torsion representation has finite dimension over the base. -/
theorem finiteDimensional_torsionField [NumberField F] :
    FiniteDimensional F ↥D.torsionField := by
  letI : IsAlgClosure F Fbar := D.closure
  have hle : D.representation.ker ≤ D.torsionField.fixingSubgroup :=
    (IntermediateField.le_iff_le D.representation.ker D.torsionField).mp le_rfl
  have hopen : IsOpen (D.torsionField.fixingSubgroup : Set (Fbar ≃ₐ[F] Fbar)) :=
    Subgroup.isOpen_mono hle D.representation_ker_isOpen
  exact (InfiniteGalois.isOpen_iff_finite D.torsionField).mp hopen

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

/-- Kernel elements fix all `ell`-torsion points by the representation characterizing law. -/
lemma galoisPoint_eq_of_mem_kernel {σ : Fbar ≃ₐ[F] Fbar}
    (hσ : σ ∈ D.representation.ker) (Q : ↥D.torsionOverClosure) :
    iutGaloisPointMap (E := E) (Fbar := Fbar) σ Q.1 = Q.1 := by
  have h := D.representation_spec σ Q
  rw [MonoidHom.mem_ker.mp hσ] at h
  simp only [Units.val_one, Matrix.one_mulVec] at h
  exact congrArg Subtype.val (D.basisOverClosure.injective h)

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

/-! ### Admissible-prime source for the q-root assembly -/

/-- The fields of IUT admissible-prime data that determine the torsion carrier used by
the q-root construction. The remaining admissible-prime conditions are not needed here. -/
structure IutAdmissiblePrimeTorsionData
    (F₀ : Type u) [Field F₀] [NumberField F₀]
    (E₀ : WeierstrassCurve F₀) [E₀.IsElliptic]
    (Fbar₀ : Type u) [Field Fbar₀] [Algebra F₀ Fbar₀]
    (ell : ℕ) where
  ell_prime : ell.Prime
  five_le : 5 ≤ ell
  closure : IsAlgClosure F₀ Fbar₀
  torsionBasis :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E₀ Fbar₀)) ell ≃+
      (Fin 2 → ZMod ell)

namespace IutAdmissiblePrimeTorsionData

variable {F₀ : Type u} [Field F₀] [NumberField F₀]
variable {E₀ : WeierstrassCurve F₀} [E₀.IsElliptic]
variable {Fbar₀ : Type u} [Field Fbar₀] [Algebra F₀ Fbar₀]
variable {ell : ℕ} (D : IutAdmissiblePrimeTorsionData F₀ E₀ Fbar₀ ell)

noncomputable def representationData : IutTorsionRepresentationData
    (F := F₀) (E := E₀) (Fbar := Fbar₀) ell :=
  IutTorsionRepresentationData.ofBasis D.closure D.torsionBasis

/-- Project the prime and torsion basis, with the chosen algebraic closure as explicit input. -/
noncomputable def ofAdmissiblePrimeData
    {VBad : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F₀ E₀))}
    (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F₀ E₀ Fbar₀ VBad)
    (closure : IsAlgClosure F₀ Fbar₀) :
    IutAdmissiblePrimeTorsionData F₀ E₀ Fbar₀ P.ℓ where
  ell_prime := P.ℓ_prime
  five_le := P.five_le
  closure := closure
  torsionBasis := P.torsionBasis

/-- The representation derived from the actual torsion basis is IUT's characterized
representation. The action law determines every matrix column by evaluating it on the
preimage of the corresponding standard basis vector. -/
theorem representation_eq_admissiblePrime
    {VBad : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F₀ E₀))}
    (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F₀ E₀ Fbar₀ VBad)
    (closure : IsAlgClosure F₀ Fbar₀) :
    (ofAdmissiblePrimeData P closure).representationData.representation = P.rep := by
  let D := ofAdmissiblePrimeData P closure
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  apply Matrix.ext
  intro i j
  let v : Fin 2 → ZMod P.ℓ := Pi.single j 1
  let Q := P.torsionBasis.symm v
  have hBasis : P.torsionBasis Q = v := by
    simp [Q]
  have hAction :
      (⟨iutGaloisPointMap (E := E₀) (Fbar := Fbar₀) σ Q.1,
        iutGaloisPointMap_torsionBy (E := E₀) (Fbar := Fbar₀) σ Q.2⟩ :
          AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E₀ Fbar₀)) P.ℓ) =
      ⟨JoshiTeich.ReferenceIut.galPointMap F₀ E₀ Fbar₀ σ Q.1,
        JoshiTeich.ReferenceIut.galPointMap_torsionBy F₀ E₀ Fbar₀ σ Q.2⟩ := by
    apply Subtype.ext
    rfl
  have hMine := D.representationData.representation_spec σ Q
  have hIut := P.rep_spec σ Q
  have hmul :
      ((D.representationData.representation σ :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod P.ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec v =
        (P.rep σ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec v := by
    calc
      _ = (D.representationData.representation σ :
          Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec (P.torsionBasis Q) := by
        rw [hBasis]
      _ = P.torsionBasis
          ⟨iutGaloisPointMap (E := E₀) (Fbar := Fbar₀) σ Q.1,
            iutGaloisPointMap_torsionBy (E := E₀) (Fbar := Fbar₀) σ Q.2⟩ := by
        simpa [D, ofAdmissiblePrimeData,
          IutAdmissiblePrimeTorsionData.representationData,
          IutTorsionRepresentationData.ofBasis] using hMine.symm
      _ = P.torsionBasis
          ⟨JoshiTeich.ReferenceIut.galPointMap F₀ E₀ Fbar₀ σ Q.1,
            JoshiTeich.ReferenceIut.galPointMap_torsionBy F₀ E₀ Fbar₀ σ Q.2⟩ := by
        rw [hAction]
      _ = (P.rep σ : Matrix (Fin 2) (Fin 2) (ZMod P.ℓ)).mulVec
          (P.torsionBasis Q) := hIut
      _ = _ := by rw [hBasis]
  have hentry := congrArg (fun w : Fin 2 → ZMod P.ℓ => w i) hmul
  simpa [v, Matrix.mulVec_single_one, Matrix.col_apply] using hentry

/-- The project and IUT fixed fields agree because their representation kernels agree. -/
theorem torsionField_eq_admissiblePrime
    {VBad : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F₀ E₀))}
    (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F₀ E₀ Fbar₀ VBad)
    (closure : IsAlgClosure F₀ Fbar₀) :
    (ofAdmissiblePrimeData P closure).representationData.torsionField =
      P.torsionField := by
  change IntermediateField.fixedField
      ((ofAdmissiblePrimeData P closure).representationData.representation.ker) =
    IntermediateField.fixedField P.rep.ker
  rw [representation_eq_admissiblePrime]

theorem ell_pos (D : IutAdmissiblePrimeTorsionData F₀ E₀ Fbar₀ ell) : 0 < ell := by
  have := D.five_le
  omega

theorem ell_odd (D : IutAdmissiblePrimeTorsionData F₀ E₀ Fbar₀ ell) : Odd ell :=
  D.ell_prime.odd_of_ne_two (by have := D.five_le; omega)

noncomputable abbrev torsionField (D : IutAdmissiblePrimeTorsionData
    F₀ E₀ Fbar₀ ell) : IntermediateField F₀ Fbar₀ :=
  D.representationData.torsionField

noncomputable instance numberField_torsionField (D : IutAdmissiblePrimeTorsionData
    F₀ E₀ Fbar₀ ell) :
    NumberField ↥D.torsionField :=
  D.representationData.numberField_torsionField

noncomputable instance instDecidableEqTorsionField (D : IutAdmissiblePrimeTorsionData
    F₀ E₀ Fbar₀ ell) : DecidableEq ↥D.torsionField :=
  D.representationData.instDecidableEqTorsionField

noncomputable def toGlobalTorsionBasis (D : IutAdmissiblePrimeTorsionData
    F₀ E₀ Fbar₀ ell) :
    IutGlobalTorsionBasis
      (E₀.map (algebraMap F₀ ↥D.torsionField)).toAffine.Point ell :=
  D.representationData.toGlobalTorsionBasis

end IutAdmissiblePrimeTorsionData

namespace IutTorsionQRootSource

variable {F : Type uF} [Field F] [NumberField F]
variable {Fbar : Type uF} [Field Fbar] [Algebra F Fbar]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {ell : ℕ} {B : IutBaseQPilotSource F ell}

/-- Build the q-root source from the admissible-prime torsion basis over the algebraic
closure. The torsion field and its rank-two basis are derived from the genuine Galois
representation; positivity and oddness of `ell` follow from the prime-data fields. -/
noncomputable def ofOverBaseBadWithCanonicalCompletionMap_ofAdmissiblePrimeAndSixTorsion
    (D : IutAdmissiblePrimeTorsionData
      F E Fbar ell)
    (B : IutBaseQPilotSource F ell)
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E))
    (S : ∀ w : iutBadPlacesOverFinset (k := F) (K := D.torsionField)
      B.badPlaces B.badPlaces_finite,
      IutTateQuotientUniformization
        (w.1.maximalIdeal.adicCompletion D.torsionField)
        (((E.map (algebraMap F D.torsionField)).map
          (NumberField.FinitePlace.embedding w.1.maximalIdeal)).toAffine.Point))
    (hq : ∀ w : iutBadPlacesOverFinset (k := F) (K := D.torsionField)
      B.badPlaces B.badPlaces_finite,
      ((S w).q : w.1.maximalIdeal.adicCompletion D.torsionField) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) :
    IutTorsionQRootSource F ↥D.torsionField ell B := by
  letI : IsAlgClosed Fbar := D.closure.isAlgClosed
  exact ofOverBaseBadWithCanonicalCompletionMap_ofWeierstrassTorsion
    B D.toGlobalTorsionBasis S hsix D.ell_pos D.ell_odd hq

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
