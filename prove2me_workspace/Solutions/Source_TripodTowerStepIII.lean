/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/Tower.lean and Iut/Tower/Main.lean
-/
import Solutions.Source_TripodTpdRamIdx
import Solutions.Source_TripodUnramified
import Solutions.Source_ReferenceIutThetaLocalBadChars
import Solutions.Source_ReferenceIutCurveTateFamily
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField
open scoped BigOperators

universe v

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}
variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)
  (hP5 : ∃ w ∈ (P.curve x).badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (anab : AnabelianExistence AG TG)
  (hcore : OrbicurveDataSection.HasCoreUniversally AG (P.curve x).F (P.curve x).E)

/-- Initial theta data assembled from the Legendre curve of the point and its Tate family. -/
noncomputable abbrev thetaDataOf : InitialThetaData AG TG :=
  (P.curve x).thetaData (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ)
    hsl hP2 hP5 ((P.modRep x ℓ hℓ).tateFamily hℓ (ne_of_gt ((by decide : 2 < 7).trans_le h7)))
    anab hcore

/-- The q-pilot for the same curve, admissible prime, and initial theta data. -/
theorem qPilotInputsOf : QPilotInputs (thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore) :=
  (P.curve x).qPilotInputs (P.arith x) (P.tate x) hℓ h7 (P.modRep x ℓ hℓ)
    hsl hP2 hP5 ((P.modRep x ℓ hℓ).tateFamily hℓ (ne_of_gt ((by decide : 2 < 7).trans_le h7)))
    anab hcore

/-- Step (iii) for the theta data assembled from the Legendre curve at this point. -/
theorem step_iii_of_curve :
    let D := thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore
    let QI := qPilotInputsOf P x hℓ h7 hsl hP2 hP5 anab hcore
    ∀ {LT : LocalTheory.{0, v} D.Kt} (TL : ThetaLocalData D LT)
      (hWild : ∀ w : FinitePlace D.Kt,
        padicValNat (AbcAdaptation.Reference.Iut.residueChar w)
          (relRamIdx w (placeTpd D.F D.E D.prime.torsionField w)) ≤
            wildConst D.ℓ (AbcAdaptation.Reference.Iut.residueChar w))
      (hRam : ∀ w : FinitePlace D.Kt,
        AbcAdaptation.Reference.Iut.residueChar w ∉ ({2, 3, 5, D.ℓ} : Finset ℕ) →
        relRamIdx w (placeTpd D.F D.E D.prime.torsionField w) ≤ 30 * D.ℓ),
      ∑ p ∈ (TL.withBadChars QI).dst, Real.log p ≤
        2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg) + 5 + Real.log D.ℓ := by
  intro D QI LT TL hWild hRam
  letI : IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField := isGalois_tpd_of_curve P x
  have hℓ2 : ℓ ≠ 2 := ne_of_gt ((by decide : 2 < 7).trans_le h7)
  have H : TowerLocalFacts D.E D.VBad D.prime := by
    refine ⟨hWild, ?_, hRam⟩
    intro w hp hgood
    exact relRamIdx_torsion_tpd_eq_one P x (P.modRep x ℓ hℓ) hℓ hℓ2 w hp hgood
  exact TL.step_iii_of_qPilotInputs QI H (relRamIdxModLeTwo_curve P x ℓ)

end AbcAdaptation.Tripod
