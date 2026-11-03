import Mathlib.Basic.ENNReal.Inv

/-!
source-id: JT-SCENE1-WITT-VALUE-PRESENTATION-COMPARISON
source: Joshi II `se:ff-rings`, weighted numerator values on localization
presentations and change of contraction.
fidelity: combines two value formulas on the same presentation relation
with their proved quotient power law. Explicit inverse functions transport
the result to the original carrier. All value functions and formulas remain explicit;
no completed-ring identity or comparison law is assumed.
Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittValuePresentationComparison

open scoped ENNReal

theorem of_presentation {X Y Z A : Type*}
    (toActual : X → Y) (fromActual : Y → X) (toStandard : X → Z)
    (actualValue : ℝ≥0∞ → Y → ℝ≥0∞)
    (standardValue : ℝ≥0∞ → Z → ℝ≥0∞)
    (P : X → ℕ → A → Prop) (d : ℕ)
    (present : ∀ x : X, ∃ (m : ℕ) (a : A), P x m a)
    (hinverse : ∀ y : Y, toActual (fromActual y) = y)
    {actualQuotient standardQuotient : ℝ≥0∞ → A → ℕ → ℝ≥0∞}
    (hactual : ∀ (ρ : ℝ≥0∞), ρ ≠ 0 → ρ ≠ ⊤ →
      ∀ (x : X) (m : ℕ) (a : A), P x m a →
        actualValue ρ (toActual x) = actualQuotient ρ a m)
    (hstandard : ∀ (ρ : ℝ≥0∞), ρ ≠ 0 → ρ ≠ ⊤ →
      ∀ (x : X) (m : ℕ) (a : A), P x m a →
        standardValue ρ (toStandard x) = standardQuotient ρ a m)
    (hquotient : ∀ (ρ : ℝ≥0∞) (a : A) (m : ℕ),
      standardQuotient ρ a m ^ d = actualQuotient (ρ ^ d) a m) :
    ∀ (ρ : ℝ≥0∞), ρ ≠ 0 → ρ ≠ ⊤ → ∀ y : Y,
      standardValue ρ (toStandard (fromActual y)) ^ d = actualValue (ρ ^ d) y := by
  intro ρ hρ0 hρtop y
  obtain ⟨m, a, ha⟩ := present (fromActual y)
  calc
    standardValue ρ (toStandard (fromActual y)) ^ d =
        standardQuotient ρ a m ^ d :=
      congrArg (fun q : ℝ≥0∞ => q ^ d) (hstandard ρ hρ0 hρtop (fromActual y) m a ha)
    _ = actualQuotient (ρ ^ d) a m := hquotient ρ a m
    _ = actualValue (ρ ^ d) (toActual (fromActual y)) :=
      (hactual (ρ ^ d) (pow_ne_zero d hρ0) (ENNReal.pow_ne_top hρtop)
        (fromActual y) m a ha).symm
    _ = actualValue (ρ ^ d) y :=
      congrArg (actualValue (ρ ^ d)) (hinverse y)

end JoshiTeich.Act1Scene1.WittValuePresentationComparison
