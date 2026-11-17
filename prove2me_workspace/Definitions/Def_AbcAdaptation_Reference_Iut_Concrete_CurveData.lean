/-
Adaptation provenance: this wrapper selects original accepted AST command spans.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Concrete/Existence.lean; Iut/Concrete/LocalTheory.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic

namespace AbcAdaptation.Reference

namespace Iut

universe u v

open NumberField WeierstrassCurve TateCurvesTheta

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-- **Tate parameters** of `E` at its multiplicative places, with uniformizers of the
completions (the interface of taxis #37). -/
structure TateInputs : Type u where
  /-- The Tate parameter `q_w` of `E` at each multiplicative place. -/
  tate : ∀ w ∈ C.badAll, TateParameter (localCompletion w)
  /-- The Tate parameter is that of `E`: the `j`-invariant of its Tate curve is `j(E)`. -/
  tateJ_eq : ∀ w (hw : w ∈ C.badAll),
    (tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j
  /-- A chosen uniformizer of each completion. -/
  unif : ∀ w ∈ C.badAll, localCompletion w
  /-- The chosen elements are uniformizers. -/
  unif_isUniformizer : ∀ w (hw : w ∈ C.badAll), IsUniformizer (unif w hw)

variable {C} in
/-- The normalized order `h_w = ord_w(q_w)` of the Tate parameter. -/
noncomputable def TateInputs.qOrder (TI : C.TateInputs) (w : FinitePlace C.F)
    (hw : w ∈ C.badAll) : ℕ :=
  ((TI.tate w hw).toOrdered (TI.unif_isUniformizer w hw)).orderNat

variable {C} in
lemma TateInputs.qOrder_pos (TI : C.TateInputs) (w : FinitePlace C.F) (hw : w ∈ C.badAll) :
    0 < TI.qOrder w hw :=
  ((TI.tate w hw).toOrdered (TI.unif_isUniformizer w hw)).orderNat_pos

open scoped Classical in
/-- **The mod-`ℓ` Galois representation** of `E` (taxis #277): a basis of `E(F̄)[ℓ]`, the
representation `ρ : Gal(F̄/F) → GL₂(𝔽_ℓ)` computing the Galois action in this basis,
and the openness of its kernel. -/
structure ModEllRepData (ℓ : ℕ) : Type u where
  /-- A chosen `𝔽_ℓ`-basis of the `ℓ`-torsion. -/
  torsionBasis :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ ≃+
      (Fin 2 → ZMod ℓ)
  /-- The mod-`ℓ` representation. -/
  rep : (C.Fbar ≃ₐ[C.F] C.Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ)
  /-- `ρ σ` is the matrix of the Galois action of `σ` in the chosen basis. -/
  rep_spec : ∀ (σ : C.Fbar ≃ₐ[C.F] C.Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ),
    torsionBasis ⟨galPointMap C.F C.E C.Fbar σ P.1, galPointMap_torsionBy C.F C.E C.Fbar σ P.2⟩ =
      (rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec (torsionBasis P)
  /-- The kernel of `ρ` is open. -/
  ker_isOpen : IsOpen (rep.ker : Set (C.Fbar ≃ₐ[C.F] C.Fbar))

end EllipticCurveData
end Iut
end AbcAdaptation.Reference
