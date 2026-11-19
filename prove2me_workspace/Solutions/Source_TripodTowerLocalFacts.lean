/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 2d8f000457da6447fa4df4bfec7365c1a49b6384
Original path Iut/Tripod/TowerFacts.lean
-/
import Solutions.Source_TripodTowerStepIII
import Solutions.Source_TripodWildRamIdx

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField
open scoped BigOperators

universe v

variable (P : CurveProviders) (x : Pt) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range)
  (hP2 : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw)

/-- The local facts on the torsion field of the admissible prime of the Legendre curve. -/
theorem towerLocalFacts_of_primeData :
    let R := P.modRep x ℓ hℓ
    let Pr := (P.curve x).primeData (P.arith x) (P.tate x) hℓ h7 R hsl hP2
    letI : NumberField ↥Pr.torsionField := R.numberField_torsionField
    TowerLocalFacts (P.curve x).E ((P.curve x).VBadOf ℓ) Pr := by
  intro R Pr
  letI : NumberField ↥Pr.torsionField := R.numberField_torsionField
  have hℓ2 : ℓ ≠ 2 := ne_of_gt ((by decide : 2 < 7).trans_le h7)
  exact ⟨padicValNat_relRamIdx_le P x R hℓ h7,
    relRamIdx_torsion_tpd_eq_one P x R hℓ hℓ2,
    relRamIdx_le_thirty_mul P x R hℓ hℓ2⟩

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}
  (hP5 : ∃ w ∈ (P.curve x).badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (anab : AnabelianExistence AG TG)
  (hcore : OrbicurveDataSection.HasCoreUniversally AG (P.curve x).F (P.curve x).E)

/-- Step (iii) for the q-pilot of the Legendre curve and its actual tower. -/
theorem step_iii_of_curve_from_source :
    let D := thetaDataOf P x hℓ h7 hsl hP2 hP5 anab hcore
    let QI := qPilotInputsOf P x hℓ h7 hsl hP2 hP5 anab hcore
    ∀ {LT : LocalTheory.{0, v} D.Kt} (TL : ThetaLocalData D LT),
      ∑ p ∈ (TL.withBadChars QI).dst, Real.log p ≤
        2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg) + 5 + Real.log D.ℓ := by
  intro D QI LT TL
  letI : IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField := isGalois_tpd_of_curve P x
  exact TL.step_iii_of_qPilotInputs QI (towerLocalFacts_of_primeData P x hℓ h7 hsl hP2)
    (relRamIdxModLeTwo_curve P x ℓ)

end AbcAdaptation.Tripod
