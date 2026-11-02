import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittExpansion
import ArithmeticTeichmullerSpaces.Act1Scene1.WittRhoPresentation

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-VALUE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`.
fidelity: defines the rho value on the standard bounded Witt localization
using only p and its primality instance. The value is the weighted digit
supremum of a p-power numerator divided by rho to the denominator exponent.
Cross multiplication proves independence of the presentation. The value
is finite for 0 < rho <= 1, separates zero, and takes p to rho.
Original proofs; no reference code copied.
boundary: Scene1/Derived; addition, submultiplicativity, topology and
Frechet completion remain open. The completed paper B is not asserted.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoValue

open PadicBoundedWittExpansion PadicBoundedWittLocalization
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

local instance coefficientField : Field (PadicTiltField.Carrier p) :=
  (PadicTiltField.carrierNormedField p).toField

abbrev Presentation (x : PadicBoundedWittLocalization.Ring p) :=
  WittRhoPresentation.Presentation (FieldWitt p) (Ambient p) p (toAmbient p x)

theorem presentation_nonempty (x : PadicBoundedWittLocalization.Ring p) :
    Nonempty (Presentation p x) := by
  obtain ⟨m, y, hy⟩ := exists_presentation p x
  exact ⟨⟨m, y, hy⟩⟩

def presentation (x : PadicBoundedWittLocalization.Ring p) : Presentation p x :=
  Classical.choice (presentation_nonempty p x)

private def coefficientValue (ρ : ℝ≥0∞) (y : FieldWitt p) : ℝ≥0∞ :=
  WittWeightedDigits.value p ρ y

private def quotientTransfer (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (z : Ambient p) (m k : ℕ) (y t : FieldWitt p)
    (hy : z * (p : Ambient p) ^ m = algebraMap (FieldWitt p) (Ambient p) y)
    (ht : z * (p : Ambient p) ^ k = algebraMap (FieldWitt p) (Ambient p) t) :
    coefficientValue p ρ y / ρ ^ m = coefficientValue p ρ t / ρ ^ k := by
  exact WittRhoPresentation.quotient_independent (R := FieldWitt p) (S := Ambient p)
    p (coefficientValue p ρ) ρ hρ0 hρtop
    (fun y n => WittWeightedDigits.value_mul_prime_pow p ρ y n) z m k y t hy ht

theorem presentation_independent (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (z : Ambient p) (m k : ℕ) (y t : FieldWitt p)
    (hy : z * (p : Ambient p) ^ m = algebraMap (FieldWitt p) (Ambient p) y)
    (ht : z * (p : Ambient p) ^ k = algebraMap (FieldWitt p) (Ambient p) t) :
    WittWeightedDigits.value p ρ y / ρ ^ m =
      WittWeightedDigits.value p ρ t / ρ ^ k :=
  quotientTransfer p ρ hρ0 hρtop
    z m k y t hy ht

def value (ρ : ℝ≥0∞) (x : PadicBoundedWittLocalization.Ring p) : ℝ≥0∞ :=
  WittWeightedDigits.value p ρ (presentation p x).numerator /
    ρ ^ (presentation p x).exponent

theorem value_eq_of_presentation (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : PadicBoundedWittLocalization.Ring p) (m : ℕ) (y : FieldWitt p)
    (hy : toAmbient p x * (p : Ambient p) ^ m =
      algebraMap (FieldWitt p) (Ambient p) y) :
    value p ρ x = WittWeightedDigits.value p ρ y / ρ ^ m :=
  presentation_independent p ρ hρ0 hρtop (toAmbient p x)
    (presentation p x).exponent m (presentation p x).numerator y
    (presentation p x).relation hy

theorem value_inclusion (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (a : PadicBoundedWittLocalization.Ainf p) :
    value p ρ (inclusion p a) = WittWeightedDigits.value p ρ (wittInclusion p a) := by
  have h := value_eq_of_presentation p ρ hρ0 hρtop (inclusion p a) 0
    (wittInclusion p a) (by simpa [ambientInclusion] using toAmbient_inclusion p a)
  simpa using h

theorem value_zero (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤) :
    value p ρ 0 = 0 := by
  have h := value_eq_of_presentation p ρ hρ0 hρtop 0 0 0 (by simp)
  simpa only [WittWeightedDigits.value_zero, pow_zero, div_one] using h

theorem value_one (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤) :
    value p ρ 1 = 1 := by
  have h := value_eq_of_presentation p ρ hρ0 hρtop 1 0 1 (by simp)
  simpa only [WittWeightedDigits.value_one, pow_zero, div_one] using h

theorem value_prime (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤) :
    value p ρ p = ρ := by
  have h := value_eq_of_presentation p ρ hρ0 hρtop p 0 p (by simp)
  simpa only [WittWeightedDigits.value_prime, pow_zero, div_one] using h

theorem value_lt_top (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : PadicBoundedWittLocalization.Ring p) : value p ρ x < ⊤ := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  obtain ⟨m, y, hy, hfin⟩ := toAmbient_exists_finite_value p ρ hρ1 x
  rw [value_eq_of_presentation p ρ hρ0 hρtop x m y hy]
  exact ENNReal.div_lt_top hfin.ne (pow_ne_zero m hρ0)

theorem value_eq_zero_iff (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : PadicBoundedWittLocalization.Ring p) : value p ρ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hn : (presentation p x).numerator = 0 := by
      rw [value, ENNReal.div_eq_zero_iff] at hx
      exact (WittWeightedDigits.value_eq_zero_iff p ρ hρ0 _).mp
        (hx.resolve_right (ENNReal.pow_ne_top hρtop))
    have hpW : (p : FieldWitt p) ≠ 0 := by
      intro hp0
      have he := WittWeightedDigits.value_prime (F := PadicTiltField.Carrier p) p 1
      rw [hp0, WittWeightedDigits.value_zero] at he
      exact zero_ne_one he
    have hp : (p : Ambient p) ≠ 0 := by
      intro hp0
      apply hpW
      apply IsFractionRing.injective (FieldWitt p) (Ambient p)
      simpa only [map_natCast, map_zero] using hp0
    apply toAmbient_injective p
    rw [map_zero]
    have he := (presentation p x).relation
    rw [hn, map_zero] at he
    exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ hp)
  · rintro rfl
    exact value_zero p ρ hρ0 hρtop

end
end JoshiTeich.Act1Scene1.PadicWittRhoValue
