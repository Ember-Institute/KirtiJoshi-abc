/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/Main.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalTheory
import Solutions.Source_ReferenceIutCurveConcreteExistence
import Solutions.Source_ReferenceIutThetaLocalData

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.CurveInputs

open WeierstrassCurve
open scoped Classical

universe u

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {K : T.CBS} {d : ℕ}
variable {CI : CurveInputs.{u} T AG K d} {x : T.Pt T.tripod}
variable {hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d} {ℓ : ℕ}

/-- The local field theory of the torsion field of this point's initial data. -/
noncomputable abbrev PointThetaData.localTheory (P : PointThetaData (TG := TG) CI x hx ℓ) :
    LocalTheory.{u, u} P.data.Kt :=
  LocalConstruct.concreteLocalTheory (K := P.data.Kt)

/-- The local theta data with the roots and q-pilot of this point's initial data. -/
noncomputable abbrev PointThetaData.localThetaData (P : PointThetaData (TG := TG) CI x hx ℓ)
    (htwo : TwoTorsionRational P.data) : ThetaLocalData P.data P.localTheory :=
  thetaLocalData P.data htwo P.localTheory P.qPilotInputs

/-- The actual local theory and Tate roots furnish the local P7 data at each point with its
chosen q-pilot. The tower input is indexed by these data. -/
theorem concreteThetaDataExistence_of_localArithmetic (CI : CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (htwo : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
      2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy (CI.curve x hx).E.toAffine.Point ((2 : ℕ) : ℤ)))
    (tower :
      ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
        (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
        (hP2 : ∀ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
          ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv w)
        (hP5 : ∃ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
          (CI.toCorollary22Inputs.localData x hx).p w ≠ 2 ∧
            (CI.toCorollary22Inputs.localData x hx).p w ≠ ℓ)
        (hsl : CI.toCorollary22Inputs.SL2Image x ℓ),
        let P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
        let TL := P.localThetaData (htwo x hx)
        TowerArithmetic P.data P.localTheory (TL.withBadChars P.qPilotInputs)) :
    ConcreteThetaDataExistence.{u, u} (AG := AG) (TG := TG) CI.toCorollary22Inputs := by
  refine CI.concreteThetaDataExistence_of_pointwise anab ?_
  intro x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  let P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  exact ⟨P.localTheory, P.localThetaData (htwo x hx), tower x hx hxe ℓ hℓ h7 hP2 hP5 hsl⟩

end AbcAdaptation.Reference.Iut.CurveInputs
