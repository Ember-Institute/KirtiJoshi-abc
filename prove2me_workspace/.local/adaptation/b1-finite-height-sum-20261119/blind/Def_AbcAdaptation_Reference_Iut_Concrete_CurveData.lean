namespace Iut

universe u v

open NumberField WeierstrassCurve TateCurvesTheta

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

structure TateInputs : Type u where

  tate : ∀ w ∈ C.badAll, TateParameter (localCompletion w)

  tateJ_eq : ∀ w (hw : w ∈ C.badAll),
    (tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j

  unif : ∀ w ∈ C.badAll, localCompletion w

  unif_isUniformizer : ∀ w (hw : w ∈ C.badAll), IsUniformizer (unif w hw)

variable {C} in

noncomputable def TateInputs.qOrder (TI : C.TateInputs) (w : FinitePlace C.F)
    (hw : w ∈ C.badAll) : ℕ :=
  ((TI.tate w hw).toOrdered (TI.unif_isUniformizer w hw)).orderNat

variable {C} in
lemma TateInputs.qOrder_pos (TI : C.TateInputs) (w : FinitePlace C.F) (hw : w ∈ C.badAll) :
    0 < TI.qOrder w hw :=
  ((TI.tate w hw).toOrdered (TI.unif_isUniformizer w hw)).orderNat_pos

open scoped Classical in

structure ModEllRepData (ℓ : ℕ) : Type u where

  torsionBasis :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ ≃+
      (Fin 2 → ZMod ℓ)

  rep : (C.Fbar ≃ₐ[C.F] C.Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ)

  rep_spec : ∀ (σ : C.Fbar ≃ₐ[C.F] C.Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ),
    torsionBasis ⟨galPointMap C.F C.E C.Fbar σ P.1, galPointMap_torsionBy C.F C.E C.Fbar σ P.2⟩ =
      (rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec (torsionBasis P)

  ker_isOpen : IsOpen (rep.ker : Set (C.Fbar ≃ₐ[C.F] C.Fbar))

end EllipticCurveData
end Iut
end AbcAdaptation.Reference
