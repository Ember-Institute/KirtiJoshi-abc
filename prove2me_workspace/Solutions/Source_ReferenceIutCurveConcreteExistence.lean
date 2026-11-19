/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Existence.lean and Iut/Tripod/Main.lean
-/
import Solutions.Source_ReferenceIutConcreteExistence
import Solutions.Source_ReferenceIutPointThetaData
import Solutions.Source_ReferenceIutThetaLocalBadChars

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.CurveInputs

universe u v

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {K : T.CBS} {d : ℕ}

/-- Assemble the concrete P7 witness from the curves and the source local inputs. -/
theorem concreteThetaDataExistence (CI : CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (LTp : ∀ D : InitialThetaData AG TG, LocalTheory.{u, v} D.Kt)
    (TLp : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt), ThetaLocalData D LT)
    (TAp : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT),
      TowerArithmetic D LT TL) :
    ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) CI.toCorollary22Inputs := by
  intro x hx hxe ℓ hℓ h7 hP2 _hP3 hP5 hsl
  obtain ⟨D, QI, hprime, hd, hq, hdiff, hc1, hc2⟩ :=
    CI.exists_initialThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  let LT := LTp D
  let TL := TLp D LT
  exact ⟨D, LT, TL, QI, TAp D LT TL, hprime, hd, hq, hdiff, hc1, hc2⟩

/-- Assemble P7 with local data on the curve and torsion field selected at each point.
The tower arithmetic uses the theta data equipped with the chosen q-pilot's bad characteristics. -/
theorem concreteThetaDataExistence_of_pointwise (CI : CurveInputs.{u} T AG K d)
    (anab : AnabelianExistence AG TG)
    (localInputs :
      ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
        (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
        (hP2 : ∀ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
          ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv w)
        (hP5 : ∃ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
          (CI.toCorollary22Inputs.localData x hx).p w ≠ 2 ∧
            (CI.toCorollary22Inputs.localData x hx).p w ≠ ℓ)
        (hsl : CI.toCorollary22Inputs.SL2Image x ℓ),
        let P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
        ∃ (LT : LocalTheory.{u, v} P.data.Kt) (TL : ThetaLocalData P.data LT),
          TowerArithmetic P.data LT (TL.withBadChars P.qPilotInputs)) :
    ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) CI.toCorollary22Inputs := by
  intro x hx hxe ℓ hℓ h7 hP2 _hP3 hP5 hsl
  let P := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  obtain ⟨LT, TL, TA⟩ := localInputs x hx hxe ℓ hℓ h7 hP2 hP5 hsl
  exact ⟨P.data, LT, TL.withBadChars P.qPilotInputs, P.qPilotInputs, TA,
    P.prime_eq, P.dmod_le, P.logQ_eq, P.logDiff_eq, P.logCond_ge, P.logCond_le⟩

end AbcAdaptation.Reference.Iut.CurveInputs
