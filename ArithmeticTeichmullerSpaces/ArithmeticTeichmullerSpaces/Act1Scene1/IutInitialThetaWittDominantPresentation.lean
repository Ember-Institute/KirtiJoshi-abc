import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitMaximum
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-DOMINANT-PRESENTATION
source: Joshi II `se:ff-rings`, the bounded rho-weighted expansions
defining the period norms before `pr:teichmuller-lift-A/B`.
fidelity: every nonzero element of the original bounded Witt localization
has an actual p-power presentation with uniformly bounded genuine digits
and a least dominant digit. The existing real rho norm equals that digit's
weighted norm divided by the same p-power weight. All witnesses come from
the proved actual bounded expansion, with no new presentation hypothesis.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; product carry analysis, multiplicative norm
equality and paper B/period/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittDominantPresentation

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion
open WittTeichmullerExpansion WittWeightedDigitMaximum
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_dominant_presentation (ρ : InitialThetaWittRhoCompletion.Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) (hx : x ≠ 0) :
    ∃ (m : ℕ) (y : FieldWitt D w) (C : ℝ) (i : ℕ),
      0 < C ∧ (∀ n, ‖digits (Arithmetic.residueChar w.1) y n‖ ≤ C) ∧
      toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
        algebraMap (FieldWitt D w) (Ambient D w) y ∧
      InitialThetaWittRhoNorm.realValue D w ρ.val x =
        ‖digits (Arithmetic.residueChar w.1) y i‖ * ρ.val.toReal ^ i / ρ.val.toReal ^ m ∧
      digits (Arithmetic.residueChar w.1) y i ≠ 0 ∧
      (∀ n, realTerm (Arithmetic.residueChar w.1) ρ.val y n ≤
        realTerm (Arithmetic.residueChar w.1) ρ.val y i) ∧
      ∀ n < i, realTerm (Arithmetic.residueChar w.1) ρ.val y n <
        realTerm (Arithmetic.residueChar w.1) ρ.val y i := by
  obtain ⟨m, y, c, C, hC, hbound, hc, he⟩ := hasBoundedExpansion D w x
  have hdigits := digits_unique (Arithmetic.residueChar w.1) y c hc
  have hybound : ∀ n, ‖digits (Arithmetic.residueChar w.1) y n‖ ≤ C := by
    intro n
    rw [← congrFun hdigits n]
    exact hbound n
  obtain ⟨i, hi, hmax, hlt⟩ := exists_first_max (Arithmetic.residueChar w.1)
    ρ.val ρ.property.2 y C hybound
  have hρtop : ρ.val ≠ ⊤ := (ρ.property.2.trans ENNReal.one_lt_top).ne
  have hnorm := InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val
    ρ.property.1.ne' hρtop x m y he
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    apply (InitialThetaWittRhoValue.value_eq_zero_iff D w ρ.val ρ.property.1.ne' hρtop x).mp
    rw [hnorm, hy0, WittWeightedDigits.value_zero, ENNReal.zero_div]
  refine ⟨m, y, C, i, hC, hybound, he, ?_,
    maximizing_digit_ne_zero (Arithmetic.residueChar w.1) ρ.val ρ.property.1.ne' y hy i hi,
    hmax, hlt⟩
  rw [InitialThetaWittRhoNorm.realValue, hnorm, hi, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_pow]

end
end JoshiTeich.Act1Scene1.InitialThetaWittDominantPresentation
