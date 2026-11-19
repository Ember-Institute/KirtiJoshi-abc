/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/ThetaLocalConstruct/Data.lean and Iut/Tripod/Tower.lean
-/
import Solutions.Source_ReferenceIutTowerStepIIIForTheta
import Solutions.Source_TripodRelativeDegreeTower

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField
open scoped BigOperators

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

/-- The residue characteristics of the bad places enumerated by the q-pilot. -/
noncomputable def QPilotInputs.badChars (QI : QPilotInputs D) : Finset ℕ :=
  QI.qPilot.badFinset.image residueChar

theorem QPilotInputs.mem_badChars (QI : QPilotInputs D) {p : ℕ} :
    p ∈ QI.badChars ↔ ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p := by
  unfold QPilotInputs.badChars
  constructor
  · rintro hp
    obtain ⟨w, hw, hwp⟩ := Finset.mem_image.mp hp
    exact ⟨w, QI.qPilot.mem_bad hw, hwp⟩
  · rintro ⟨w, hw, hwp⟩
    exact Finset.mem_image.mpr ⟨w, QI.bad_finite.mem_toFinset.mpr hw, hwp⟩

private lemma badChar_of_liesOver (QI : QPilotInputs D) (v : FinitePlace D.Kt)
    (w : FinitePlace D.F) (hvw : FinitePlace.LiesOver v w)
    (hw : w ∈ badPlacesOver D.F D.E D.VBad) : residueChar v ∈ QI.badChars :=
  QI.mem_badChars.mpr ⟨w, hw, (Tripod.residueChar_eq_of_liesOver hvw).symm⟩

private noncomputable def qrootOnBadChars (QI : QPilotInputs D) (TL : ThetaLocalData D LT)
    (w : FinitePlace D.Kt) : completionAt D.Kt w :=
  if residueChar w ∈ QI.badChars then TL.qroot w else 1

/-- Use the q-pilot's actual bad characteristics with the Tate roots of the same data. -/
noncomputable def ThetaLocalData.withBadChars (TL : ThetaLocalData D LT)
    (QI : QPilotInputs D) : ThetaLocalData D LT where
  badChars := QI.badChars
  qroot := qrootOnBadChars QI TL
  qroot_ne_zero w := by
    unfold qrootOnBadChars
    split_ifs
    · exact TL.qroot_ne_zero w
    · exact one_ne_zero
  ordp_qroot_nonneg w := by
    unfold qrootOnBadChars
    split_ifs
    · exact TL.ordp_qroot_nonneg w
    · simp [ordp]
  qroot_eq_one w hw := by simp only [qrootOnBadChars, if_neg hw]
  embedF := TL.embedF
  qroot_pow w z h hz := by
    rw [qrootOnBadChars, if_pos (badChar_of_liesOver QI w z h hz)]
    exact TL.qroot_pow w z h hz
  ordp_qroot w z h hz := by
    rw [qrootOnBadChars, if_pos (badChar_of_liesOver QI w z h hz)]
    exact TL.ordp_qroot w z h hz
  residueChar_mem := badChar_of_liesOver QI
  bad_residueChar_mem w hw := QI.mem_badChars.mpr ⟨w, hw, rfl⟩
  badChars_prime p hp := by
    obtain ⟨w, _, hwp⟩ := QI.mem_badChars.mp hp
    rw [← hwp]
    exact Tripod.residueChar_prime w
  sum_weight_ordp_qroot p bad hbad := by
    by_cases hp : (p : ℕ) ∈ QI.badChars
    · refine (Finset.sum_congr rfl fun w _ => ?_).trans (TL.sum_weight_ordp_qroot p bad hbad)
      have hw := LT.residueChar_fiberPlace (p := p) w
      rw [qrootOnBadChars, if_pos (hw.symm ▸ hp)]
    · have hempty : bad.attach.filter (fun w => residueChar w.1 = (p : ℕ)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        intro w _ hwp
        exact hp (QI.mem_badChars.mpr ⟨w.1, hbad ▸ Finset.mem_coe.mpr w.2, hwp⟩)
      rw [hempty, Finset.sum_empty, zero_div]
      refine Finset.sum_eq_zero fun w _ => ?_
      have hw := LT.residueChar_fiberPlace (p := p) w
      rw [qrootOnBadChars, if_neg (hw.symm ▸ hp)]
      simp [ordp]

/-- Every bad characteristic of the constructed theta data has an actual bad-place witness. -/
theorem ThetaLocalData.exists_badPlace_of_mem_withBadChars (TL : ThetaLocalData D LT)
    (QI : QPilotInputs D) (p : ℕ) (hp : p ∈ (TL.withBadChars QI).badChars) :
    ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p :=
  QI.mem_badChars.mp hp

/-- Step (iii) for the local theta data equipped with the q-pilot's bad characteristics. -/
theorem ThetaLocalData.step_iii_of_qPilotInputs (TL : ThetaLocalData D LT) (QI : QPilotInputs D)
    (H : TowerLocalFacts D.E D.VBad D.prime) (he2 : RelRamIdxModLeTwo D.E D.VBad)
    [IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField] :
    ∑ p ∈ (TL.withBadChars QI).dst, Real.log p ≤
      2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg) + 5 + Real.log D.ℓ :=
  (TL.withBadChars QI).step_iii_of_localFacts H he2 QI.bad_finite
    (TL.exists_badPlace_of_mem_withBadChars QI)

end AbcAdaptation.Reference.Iut
