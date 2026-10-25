import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-WEIGHTED-DIGITS
source: Joshi II `se:ff-rings`, the bounded Witt localization and
rho-weighted expansions for `pr:teichmuller-lift-A/B`.
fidelity: every element of the actual bounded Witt localization admits a
p-power denominator presentation whose unique digits have finite weighted
supremum at every radius at most one. The weights and prime-shift law use
the actual perfect tilt and its original norm. Original proofs.
boundary: Scene1/Derived; this supplies finite coefficient values on actual
presentations, not yet a presentation-independent norm on the localization
or the completed Frechet B. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittWeightedDigits

open JoshiTeich.Prologue
open scoped ENNReal
open InitialThetaBoundedWittExpansion InitialThetaBoundedWittLocalization
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem boundedExpansion_exists_finite_value (ρ : ℝ≥0∞) (hρ : ρ ≤ 1)
    (z : Ambient D w) (hz : HasBoundedExpansion D w z) :
    ∃ m : ℕ, ∃ y : FieldWitt D w,
      z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
        algebraMap (FieldWitt D w) (Ambient D w) y ∧
      WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ y < ⊤ := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz⟩ := hz
  refine ⟨m, y, hz, ?_⟩
  apply WittWeightedDigits.value_lt_top_of_bound (Arithmetic.residueChar w.1) ρ hρ y C
  have he := WittTeichmullerExpansion.digits_unique (Arithmetic.residueChar w.1) y c hc
  intro n
  rw [← congrFun he n]
  exact hbound n

theorem toAmbient_exists_finite_value (ρ : ℝ≥0∞) (hρ : ρ ≤ 1)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    ∃ m : ℕ, ∃ y : FieldWitt D w,
      toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
        algebraMap (FieldWitt D w) (Ambient D w) y ∧
      WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ y < ⊤ :=
  boundedExpansion_exists_finite_value D w ρ hρ _ (hasBoundedExpansion D w x)

theorem teichmuller_varpi_value (ρ : ℝ≥0∞) :
    WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ
      (WittVector.teichmuller (Arithmetic.residueChar w.1)
        (varpi D w : InitialThetaTiltField.Carrier D w)) =
      ENNReal.ofReal ‖(varpi D w : InitialThetaTiltField.Carrier D w)‖ :=
  WittWeightedDigits.value_teichmuller (Arithmetic.residueChar w.1) ρ _

theorem fieldWitt_mul_prime_value (ρ : ℝ≥0∞) (y : FieldWitt D w) :
    WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ
        (y * (Arithmetic.residueChar w.1 : FieldWitt D w)) =
      ρ * WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ y :=
  WittWeightedDigits.value_mul_prime (Arithmetic.residueChar w.1) ρ y

end
end JoshiTeich.Act1Scene1.InitialThetaWittWeightedDigits
