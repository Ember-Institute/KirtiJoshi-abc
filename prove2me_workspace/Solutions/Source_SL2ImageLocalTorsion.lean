/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/SL2Image.lean and Iut/Cor312/ThetaData/PointMap.lean
-/
import Solutions.Source_ModEllRepGalois
import Solutions.Source_ReferenceIutTateTorsion
import Solutions.Source_SL2ImageLocalValuation

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField WeierstrassCurve Anabelian
open scoped Classical Valued

universe u

noncomputable section

variable (C : EllipticCurveData.{u}) {ℓ : ℕ} (R : C.ModEllRepData ℓ)

local instance (priority := 1100) instDecidableEqTorsionFieldLocal :
    DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- Base change to the completion embeds global torsion into local torsion. -/
lemma card_torsion_curveKw_ge (w' : FinitePlace ↥R.torsionField)
    [Finite ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w'))] :
    ℓ * ℓ ≤ Nat.card ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) := by
  let f : ↥R.TK →+ ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) :=
    ((pointMap (curveK C.E R.torsionField) (emb R.torsionField w')).domRestrict R.TK).codRestrict _
      (fun P => by
        rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
        have hP : ℓ • P = 0 := Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp P.2)
        rw [hP, map_zero])
  have hpoint : Function.Injective
      (pointMap (curveK C.E R.torsionField) (emb R.torsionField w')) := by
    letI := (emb R.torsionField w').toAlgebra
    exact Affine.Point.map_injective (W' := curveK C.E R.torsionField)
      (S := ↥R.torsionField) (F := ↥R.torsionField) (K := localCompletion w')
      (Algebra.ofId ↥R.torsionField (localCompletion w'))
  have hf : Function.Injective f := fun P P' h => by
    apply Subtype.ext
    apply hpoint
    have h' := congrArg Subtype.val h
    simpa only [f, AddMonoidHom.codRestrict_apply, AddMonoidHom.domRestrict_apply] using h'
  calc
    ℓ * ℓ = Nat.card ↥R.TK := by rw [R.card_torsionBy_EK, sq]
    _ ≤ _ := Nat.card_le_card_of_injective f hf

/-- A Tate structure over the torsion field completion supplies the root class needed
for divisibility of the relative ramification index. -/
theorem prime_dvd_ramificationIdx_of_tateStructure (TI : C.TateInputs) (hℓ : ℓ.Prime)
    {w : FinitePlace C.F} (hw : w ∈ C.badAll) (hP2 : ¬ ℓ ∣ TI.qOrder w hw)
    {w' : FinitePlace ↥R.torsionField} (hw'w : FinitePlace.LiesOver w' w)
    (S : TateStructure (curveKw C.E R.torsionField w')) :
    ℓ ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Finite ↥(TateStructure.torsion ℓ (curveKw C.E R.torsionField w')) :=
    S.finite_torsion ℓ
  obtain ⟨u, m, hu⟩ := S.exists_root_class ℓ (C.card_torsion_curveKw_ge R w')
  exact C.prime_dvd_ramificationIdx_of_root_class TI hℓ R hw hP2 hw'w S u m hu

end

end AbcAdaptation.Reference.Iut.EllipticCurveData
