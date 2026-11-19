/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Existence.lean and Iut/Concrete/ThetaRegion.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide
import Solutions.Source_ReferenceIutInitialThetaData
import Solutions.Source_SL2ImageLocalTate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField
open scoped Classical

universe u

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The finiteness and degree inputs for the concrete `q`-pilot of `D`. -/
structure QPilotInputs (D : InitialThetaData AG TG) : Prop where
  bad_finite : (badPlacesOver D.F D.E D.VBad).Finite
  inertDeg_pos : ∀ w : FinitePlace D.F, 0 < inertDeg D.F w

/-- The `q`-pilot weights the bad places by their residue degrees divided by the field degree. -/
noncomputable def QPilotInputs.qPilot {D : InitialThetaData AG TG}
    (QI : QPilotInputs D) : QPilotData D where
  badFinset := QI.bad_finite.toFinset
  badFinset_spec := QI.bad_finite.coe_toFinset
  weight w := (inertDeg D.F w : ℝ) / Module.finrank ℚ D.F
  weight_pos w _ := by
    have hdeg : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    exact div_pos (by exact_mod_cast QI.inertDeg_pos w) (by exact_mod_cast hdeg)

namespace EllipticCurveData

variable (C : EllipticCurveData.{u}) (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ}
  (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (R : C.ModEllRepData ℓ)
  (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
  (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw)
  (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ)
  (TF : TateFamily C.E R.torsionField ℓ (C.VBadOf ℓ))
  (anab : AnabelianExistence AG TG) (hcore : OrbicurveDataSection.HasCoreUniversally AG C.F C.E)

/-- Finiteness and degree positivity for the `q`-pilot of the assembled initial Θ-data. -/
theorem qPilotInputs : QPilotInputs (C.thetaData CA TI hℓ h7 R hsl hP2 hP5 TF anab hcore) where
  bad_finite := CA.badAll_finite.subset fun _ hw => C.mem_badAll_of_mem_badPlacesOver hw
  inertDeg_pos := CA.inertDeg_pos

/-- The `q`-pilot logarithm equals the part of the curve's height away from `2` and `ℓ`. -/
theorem logQ_eq :
    (C.qPilotInputs CA TI hℓ h7 R hsl hP2 hP5 TF anab hcore).qPilot.logQ =
      (C.localHeightData CA TI).heightOther 2 ℓ := by
  have hfin : (badPlacesOver C.F C.E (C.VBadOf ℓ)).Finite :=
    CA.badAll_finite.subset fun _ hw => C.mem_badAll_of_mem_badPlacesOver hw
  change ∑ w ∈ hfin.toFinset.attach,
      ((inertDeg C.F w.1 : ℝ) / Module.finrank ℚ C.F) *
        ((TI.qOrder w.1 (C.mem_badAll_of_mem_badPlacesOver (hfin.mem_toFinset.mp w.2)) : ℕ) : ℝ) *
        Real.log (residueChar w.1) =
    (∑ w ∈ CA.badAll_finite.toFinset.filter (fun w => residueChar w ≠ 2 ∧ residueChar w ≠ ℓ),
      (((if h : w ∈ C.badAll then TI.qOrder w h else 0 : ℕ) : ℝ) * (inertDeg C.F w : ℝ) *
        Real.log (residueChar w))) / Module.finrank ℚ C.F
  have hfinset : hfin.toFinset =
      CA.badAll_finite.toFinset.filter (fun w => residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    exact Set.ext_iff.mp (C.badPlacesOver_VBadOf CA) w
  rw [Finset.sum_div]
  refine (Finset.sum_congr rfl (g := fun w => ((inertDeg C.F w.1 : ℝ) / Module.finrank ℚ C.F) *
      ((if h : w.1 ∈ C.badAll then TI.qOrder w.1 h else 0 : ℕ) : ℝ) *
      Real.log (residueChar w.1)) fun w _ => ?_).trans ?_
  · rw [dif_pos (C.mem_badAll_of_mem_badPlacesOver (hfin.mem_toFinset.mp w.2))]
  · rw [Finset.sum_attach _ (fun w => ((inertDeg C.F w : ℝ) / Module.finrank ℚ C.F) *
      ((if h : w ∈ C.badAll then TI.qOrder w h else 0 : ℕ) : ℝ) *
      Real.log (residueChar w)), hfinset]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end EllipticCurveData
end AbcAdaptation.Reference.Iut
