import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittWeightedDigits

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-VALUE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the
rho-weighted Teichmuller expansions of the bounded period subring.
fidelity: divides the weighted digit supremum of a p-power numerator by
rho to the denominator exponent. Cross multiplication in the actual
fraction field proves independence of the presentation. On the actual
bounded Witt localization the resulting value is finite for 0<rho<=1,
separates zero, and takes p to rho. Original proofs; no reference code copied.
boundary: Scene1/Derived; addition/submultiplicativity, Frobenius continuity
and Frechet completion remain open. No completed B or BK identity asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoValue

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion InitialThetaBoundedWittLocalization
open scoped ENNReal
noncomputable section
universe u
structure PrimePresentation (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) (z : S) where
  exponent : ℕ
  numerator : R
  relation : z * (p : S) ^ exponent = algebraMap R S numerator

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Presentation (x : InitialThetaBoundedWittLocalization.Ring D w) :=
  PrimePresentation (FieldWitt D w) (Ambient D w) (Arithmetic.residueChar w.1)
    (toAmbient D w x)

theorem presentation_nonempty (x : InitialThetaBoundedWittLocalization.Ring D w) :
    Nonempty (Presentation D w x) := by
  obtain ⟨m, y, c, C, hC, hbound, hc, he⟩ := hasBoundedExpansion D w x
  exact ⟨⟨m, y, he⟩⟩

def presentation (x : InitialThetaBoundedWittLocalization.Ring D w) : Presentation D w x :=
  Classical.choice (presentation_nonempty D w x)

theorem numerator_cross_eq (z : Ambient D w) (m k : ℕ) (y t : FieldWitt D w)
    (hy : z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) y)
    (ht : z * (Arithmetic.residueChar w.1 : Ambient D w) ^ k =
      algebraMap (FieldWitt D w) (Ambient D w) t) :
    y * (Arithmetic.residueChar w.1 : FieldWitt D w) ^ k =
      t * (Arithmetic.residueChar w.1 : FieldWitt D w) ^ m := by
  apply IsFractionRing.injective (FieldWitt D w) (Ambient D w)
  simp only [map_mul, map_pow, map_natCast]
  rw [← hy, ← ht]
  exact mul_right_comm z _ _

theorem presentation_independent (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (z : Ambient D w) (m k : ℕ) (y t : FieldWitt D w)
    (hy : z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) y)
    (ht : z * (Arithmetic.residueChar w.1 : Ambient D w) ^ k =
      algebraMap (FieldWitt D w) (Ambient D w) t) :
    WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ y / ρ ^ m =
      WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ t / ρ ^ k := by
  apply (ENNReal.div_eq_div_iff (pow_ne_zero k hρ0) (ENNReal.pow_ne_top hρtop)
    (pow_ne_zero m hρ0) (ENNReal.pow_ne_top hρtop)).mpr
  have he := congrArg (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ)
    (numerator_cross_eq D w z m k y t hy ht)
  simpa only [WittWeightedDigits.value_mul_prime_pow] using he

def value (ρ : ℝ≥0∞) (x : InitialThetaBoundedWittLocalization.Ring D w) : ℝ≥0∞ :=
  WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ (presentation D w x).numerator /
    ρ ^ (presentation D w x).exponent

theorem value_eq_of_presentation (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaBoundedWittLocalization.Ring D w) (m : ℕ) (y : FieldWitt D w)
    (hy : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) y) :
    value D w ρ x = WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ y / ρ ^ m :=
  presentation_independent D w ρ hρ0 hρtop (toAmbient D w x)
    (presentation D w x).exponent m (presentation D w x).numerator y
    (presentation D w x).relation hy

theorem value_inclusion (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤) (a : InitialThetaTiltFontaine.Ainf D w) :
    value D w ρ (inclusion D w a) =
      WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ (wittInclusion D w a) := by
  have h := value_eq_of_presentation D w ρ hρ0 hρtop (inclusion D w a) 0
    (wittInclusion D w a) (by simpa [ambientInclusion] using toAmbient_inclusion D w a)
  simpa using h

theorem value_zero (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤) : value D w ρ 0 = 0 := by
  have h := value_eq_of_presentation D w ρ hρ0 hρtop 0 0 0 (by simp)
  simpa only [WittWeightedDigits.value_zero, pow_zero, div_one] using h

theorem value_one (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤) : value D w ρ 1 = 1 := by
  have h := value_eq_of_presentation D w ρ hρ0 hρtop 1 0 1 (by simp)
  simpa only [WittWeightedDigits.value_one, pow_zero, div_one] using h

theorem value_prime (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤) :
    value D w ρ (Arithmetic.residueChar w.1) = ρ := by
  have h := value_eq_of_presentation D w ρ hρ0 hρtop (Arithmetic.residueChar w.1) 0
    (Arithmetic.residueChar w.1) (by simp)
  simpa only [WittWeightedDigits.value_prime, pow_zero, div_one] using h

theorem value_lt_top (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≤ 1)
    (x : InitialThetaBoundedWittLocalization.Ring D w) : value D w ρ x < ⊤ := by
  have hρtop : ρ ≠ ⊤ := (hρ1.trans_lt ENNReal.one_lt_top).ne
  obtain ⟨m, y, hy, hfin⟩ :=
    InitialThetaWittWeightedDigits.toAmbient_exists_finite_value D w ρ hρ1 x
  rw [value_eq_of_presentation D w ρ hρ0 hρtop x m y hy]
  exact ENNReal.div_lt_top hfin.ne (pow_ne_zero m hρ0)

theorem value_eq_zero_iff (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaBoundedWittLocalization.Ring D w) : value D w ρ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hn : (presentation D w x).numerator = 0 := by
      rw [value, ENNReal.div_eq_zero_iff] at hx
      exact (WittWeightedDigits.value_eq_zero_iff (Arithmetic.residueChar w.1) ρ hρ0 _).mp
        (hx.resolve_right (ENNReal.pow_ne_top hρtop))
    have hpW : (Arithmetic.residueChar w.1 : FieldWitt D w) ≠ 0 := by
      intro hp0
      have he := WittWeightedDigits.value_prime
        (F := InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1) 1
      rw [hp0, WittWeightedDigits.value_zero] at he
      exact zero_ne_one he
    have hp : (Arithmetic.residueChar w.1 : Ambient D w) ≠ 0 := by
      intro hp0
      apply hpW
      apply IsFractionRing.injective (FieldWitt D w) (Ambient D w)
      simpa only [map_natCast, map_zero] using hp0
    apply toAmbient_injective D w
    rw [map_zero]
    have he := (presentation D w x).relation
    rw [hn, map_zero] at he
    exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ hp)
  · rintro rfl
    exact value_zero D w ρ hρ0 hρtop

theorem value_mul_prime (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    value D w ρ (x * Arithmetic.residueChar w.1) = ρ * value D w ρ x := by
  let P := presentation D w x
  have he : toAmbient D w (x * Arithmetic.residueChar w.1) *
      (Arithmetic.residueChar w.1 : Ambient D w) ^ P.exponent =
      algebraMap (FieldWitt D w) (Ambient D w)
        (P.numerator * (Arithmetic.residueChar w.1 : FieldWitt D w)) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]
    calc
      _ = (toAmbient D w x *
          (Arithmetic.residueChar w.1 : Ambient D w) ^ P.exponent) *
          Arithmetic.residueChar w.1 := by ac_rfl
      _ = _ := congrArg (fun z : Ambient D w => z * Arithmetic.residueChar w.1) P.relation
  rw [value_eq_of_presentation D w ρ hρ0 hρtop _ P.exponent _ he,
    WittWeightedDigits.value_mul_prime]
  change (ρ * WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ P.numerator) /
    ρ ^ P.exponent = ρ * (WittWeightedDigits.value (Arithmetic.residueChar w.1) ρ P.numerator /
      ρ ^ P.exponent)
  simp only [div_eq_mul_inv, mul_assoc]

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoValue
