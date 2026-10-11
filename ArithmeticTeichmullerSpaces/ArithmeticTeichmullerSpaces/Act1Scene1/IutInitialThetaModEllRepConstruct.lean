/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/ModEllRepConstruct.lean`
original-author: The iut contributors
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapts the Galois action and open-kernel representation
construction to the local `IutCurveModEllRepData` contract. No reference
project import is used; the SL2 image condition remains a separate input.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaMaximalPrimeData
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlacesOver

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField WeierstrassCurve
open scoped Classical

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-MODELLREP-CONSTRUCT
source: `refer/iut/Iut/Concrete/ModEllRepConstruct.lean`,
`galTorsionHom`, `repOf`, `repOf_spec`, and `repOf_ker_isOpen`.
fidelity: constructs the mod-ell representation from an explicit torsion
basis and proves that its kernel is open. The construction does not prove
that the image contains SL2; that condition is retained as a separate input.
boundary: Scene1/Derived
-/

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

lemma iutGalPointMap_one (P : Affine.Point (Affine.baseChange E Fbar)) :
    JoshiTeich.ReferenceIut.galPointMap F E Fbar 1 P = P := by
  cases P <;> rfl

lemma iutGalPointMap_mul (σ τ : Fbar ≃ₐ[F] Fbar)
    (P : Affine.Point (Affine.baseChange E Fbar)) :
    JoshiTeich.ReferenceIut.galPointMap F E Fbar (σ * τ) P =
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ
        (JoshiTeich.ReferenceIut.galPointMap F E Fbar τ P) := by
  cases P <;> rfl

/-- The Galois action on the `ell`-torsion subgroup. -/
noncomputable def iutGalTorsionHom (ell : ℕ) (σ : Fbar ≃ₐ[F] Fbar) :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell →+
      AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell :=
  ((JoshiTeich.ReferenceIut.galPointMap F E Fbar σ).domRestrict
    (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell)).codRestrict
    (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell)
    (fun P => JoshiTeich.ReferenceIut.galPointMap_torsionBy F E Fbar σ P.2)

@[simp] theorem iutGalTorsionHom_apply (ell : ℕ) (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) :
    iutGalTorsionHom E Fbar ell σ P =
      ⟨JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P.1,
        JoshiTeich.ReferenceIut.galPointMap_torsionBy F E Fbar σ P.2⟩ := by
  rfl

variable (ell : ℕ)
variable (b : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
  (Fin 2 → ZMod ell))

noncomputable def iutRepLin (σ : Fbar ≃ₐ[F] Fbar) :
    Module.End (ZMod ell) (Fin 2 → ZMod ell) :=
  (b.toAddMonoidHom.comp
    ((iutGalTorsionHom E Fbar ell σ).comp b.symm.toAddMonoidHom)).toZModLinearMap ell

lemma iutRepLin_apply (σ : Fbar ≃ₐ[F] Fbar) (v : Fin 2 → ZMod ell) :
    iutRepLin E Fbar ell b σ v =
      b (iutGalTorsionHom E Fbar ell σ (b.symm v)) := rfl

noncomputable def iutRepEnd :
    (Fbar ≃ₐ[F] Fbar) →* Module.End (ZMod ell) (Fin 2 → ZMod ell) where
  toFun := iutRepLin E Fbar ell b
  map_one' := by
    refine LinearMap.ext fun v => ?_
    rw [iutRepLin_apply, Module.End.one_apply]
    have h : iutGalTorsionHom E Fbar ell 1 (b.symm v) = b.symm v := by
      rw [iutGalTorsionHom_apply]
      exact Subtype.ext (iutGalPointMap_one E Fbar _)
    rw [h, b.apply_symm_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, iutRepLin_apply, iutRepLin_apply,
      iutRepLin_apply, b.symm_apply_apply]
    congr 1
    exact Subtype.ext (iutGalPointMap_mul E Fbar σ τ _)

noncomputable def iutRepOf :
    (Fbar ≃ₐ[F] Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ell) :=
  (Units.mapEquiv (LinearMap.toMatrixAlgEquiv' :
    Module.End (ZMod ell) (Fin 2 → ZMod ell) ≃ₐ[ZMod ell]
      Matrix (Fin 2) (Fin 2) (ZMod ell)).toMulEquiv).toMonoidHom.comp
    (iutRepEnd E Fbar ell b).toHomUnits

lemma iutRepOf_coe (σ : Fbar ≃ₐ[F] Fbar) :
    (iutRepOf E Fbar ell b σ : Matrix (Fin 2) (Fin 2) (ZMod ell)) =
      LinearMap.toMatrix' (iutRepEnd E Fbar ell b σ) := rfl

theorem iutRepOf_spec (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) :
    b ⟨JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P.1,
        JoshiTeich.ReferenceIut.galPointMap_torsionBy F E Fbar σ P.2⟩ =
      (iutRepOf E Fbar ell b σ : Matrix (Fin 2) (Fin 2) (ZMod ell)).mulVec (b P) := by
  rw [iutRepOf_coe, LinearMap.toMatrix'_mulVec]
  show _ = iutRepLin E Fbar ell b σ (b P)
  rw [iutRepLin_apply, b.symm_apply_apply, iutGalTorsionHom_apply]

private lemma iutRepOf_mem_ker_of_fixed (σ : Fbar ≃ₐ[F] Fbar)
    (hσ : ∀ P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P.1 = P.1) :
    σ ∈ (iutRepOf E Fbar ell b).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [iutRepOf_coe, Units.val_one, ← LinearMap.toMatrix'_one]
  congr 1
  refine LinearMap.ext fun v => ?_
  change iutRepLin E Fbar ell b σ v = v
  rw [iutRepLin_apply]
  have h : iutGalTorsionHom E Fbar ell σ (b.symm v) = b.symm v := by
    rw [iutGalTorsionHom_apply]
    exact Subtype.ext (hσ _)
  rw [h, b.apply_symm_apply]

private lemma iutIsOpen_galPointMap_eq
    (P : Affine.Point (Affine.baseChange E Fbar)) :
    IsOpen {σ : Fbar ≃ₐ[F] Fbar |
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P = P} := by
  rcases P with _ | ⟨x, y, h⟩
  · have htop : {σ : Fbar ≃ₐ[F] Fbar |
        JoshiTeich.ReferenceIut.galPointMap F E Fbar σ .zero = .zero} = Set.univ :=
      Set.eq_univ_of_forall fun _ => rfl
    rw [htop]
    exact isOpen_univ
  · have hset : {σ : Fbar ≃ₐ[F] Fbar |
        JoshiTeich.ReferenceIut.galPointMap F E Fbar σ (.some x y h) = .some x y h} =
        {σ | σ x = x} ∩ {σ | σ y = y} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff,
        JoshiTeich.ReferenceIut.galPointMap, Affine.Point.map_some,
        Affine.Point.some.injEq, AlgEquiv.coe_toAlgHom]
    rw [hset]
    exact (JoshiTeich.ReferenceIut.isOpen_eval_eq F Fbar x x).inter
      (JoshiTeich.ReferenceIut.isOpen_eval_eq F Fbar y y)

theorem iutRepOf_ker_isOpen [NeZero ell] :
    IsOpen ((iutRepOf E Fbar ell b).ker : Set (Fbar ≃ₐ[F] Fbar)) := by
  haveI : Finite (AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell) :=
    Finite.of_equiv _ b.symm.toEquiv
  have hS : IsOpen (⋂ P : AddSubgroup.torsionBy
      (Affine.Point (Affine.baseChange E Fbar)) ell,
      {σ : Fbar ≃ₐ[F] Fbar |
        JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P.1 = P.1}) :=
    isOpen_iInter_of_finite fun P => iutIsOpen_galPointMap_eq E Fbar P.1
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset (hS.mem_nhds ?_) ?_)
  · simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact fun P => iutGalPointMap_one E Fbar P.1
  · intro σ hσ
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hσ
    exact iutRepOf_mem_ker_of_fixed E Fbar ell b σ (fun P => hσ P)

/-- Construct representation data from a chosen basis of actual elliptic torsion. -/
noncomputable def IutCurveModEllRepData.ofBasis [NeZero ell]
    (hbasis : Nonempty (AddSubgroup.torsionBy
      (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell))) :
    IutCurveModEllRepData F E Fbar ell where
  torsionBasis := hbasis.some
  rep := iutRepOf E Fbar ell hbasis.some
  rep_spec := iutRepOf_spec E Fbar ell hbasis.some
  ker_isOpen := iutRepOf_ker_isOpen E Fbar ell hbasis.some

end

end JoshiTeich.Act1Scene1
