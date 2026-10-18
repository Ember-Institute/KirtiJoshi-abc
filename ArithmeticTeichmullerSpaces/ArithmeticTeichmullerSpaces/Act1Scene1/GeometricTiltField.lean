import ArithmeticTeichmullerSpaces.Act1Scene1.AlgebraicallyClosedFontaine
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharP.Algebra

/-!
source-id: JT-SCENE1-GEOMETRIC-TILT-FIELD
source: Joshi, Arithmetic Holomorphic Structures, tilt after lem:perfectoid;
Mathlib PreTilt.val, PreTilt.isDomain, Tilt and valuation localization.
fidelity: constructs the fraction field of the actual pretilt, proves its
characteristic p and perfectness, and extends the actual pretilt valuation.
The field is Mathlib's algebraic Tilt carrier. Completeness, algebraic
closedness of the tilt and an identification with a selected paper tilt are
not asserted. Original proofs; no reference source code copied.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricTiltField

open JoshiTeich.Prologue
open scoped NNReal
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

abbrev Source := PreTilt (LocalGeometricFontaine.integerRing Ω) p

/-- The actual perfection of O/(p) is a domain, by its norm valuation. -/
instance source_isDomain : IsDomain (Source Ω p) :=
  PreTilt.isDomain Ω (NormedField.valuation (K := Ω))
    (LocalGeometricFontaine.integerRing Ω) (Valuation.integer.integers _) p

def sourceValuation : Valuation (Source Ω p) ℝ≥0 :=
  PreTilt.val Ω (NormedField.valuation (K := Ω))
    (LocalGeometricFontaine.integerRing Ω) (Valuation.integer.integers _) p

theorem sourceValuation_eq_zero_iff (x : Source Ω p) : sourceValuation Ω p x = 0 ↔ x = 0 :=
  PreTilt.map_eq_zero (Valuation.integer.integers _)

abbrev FractionField := FractionRing (Source Ω p)

instance fractionField_charP : CharP (FractionField Ω p) p :=
  charP_of_injective_ringHom (IsFractionRing.injective (Source Ω p) (FractionField Ω p)) p

instance fractionField_perfect : PerfectRing (FractionField Ω p) p := by
  apply PerfectRing.ofSurjective (FractionField Ω p) p
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (Source Ω p) x
  obtain ⟨a', ha⟩ := (PerfectRing.bijective_frobenius (R := Source Ω p) (p := p)).surjective a
  obtain ⟨b', hb⟩ := (PerfectRing.bijective_frobenius (R := Source Ω p) (p := p)).surjective b
  change a' ^ p = a at ha
  change b' ^ p = b at hb
  refine ⟨algebraMap (Source Ω p) (FractionField Ω p) a' /
    algebraMap (Source Ω p) (FractionField Ω p) b', ?_⟩
  rw [frobenius_def, div_pow, ← map_pow, ← map_pow, ha, hb]

/-- Every denominator in the fraction ring has nonzero actual pretilt valuation. -/
theorem denominators_le_primeCompl :
    nonZeroDivisors (Source Ω p) ≤ (sourceValuation Ω p).supp.primeCompl := by
  intro x hx
  change sourceValuation Ω p x ≠ 0
  exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hx)
    ((sourceValuation_eq_zero_iff Ω p x).mp h)

def fractionValuation : Valuation (FractionField Ω p) ℝ≥0 :=
  (sourceValuation Ω p).extendToLocalization (denominators_le_primeCompl Ω p) (FractionField Ω p)

theorem fractionValuation_inclusion (x : Source Ω p) :
    fractionValuation Ω p (algebraMap (Source Ω p) (FractionField Ω p) x) = sourceValuation Ω p x :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ x

theorem fractionValuation_div (a b : Source Ω p) :
    fractionValuation Ω p (algebraMap (Source Ω p) (FractionField Ω p) a /
      algebraMap (Source Ω p) (FractionField Ω p) b) =
        sourceValuation Ω p a / sourceValuation Ω p b := by
  rw [map_div₀, fractionValuation_inclusion, fractionValuation_inclusion]

local instance primeValuation_ne_one : Fact ((NormedField.valuation (K := Ω)) (p : Ω) ≠ 1) := by
  constructor
  change ‖(p : Ω)‖₊ ≠ 1
  intro h
  exact hp.out.2.ne (congrArg (fun r : ℝ≥0 => (r : ℝ)) h)

/-- Identifies the constructed fraction-field carrier with Mathlib's Tilt definition. -/
theorem fractionField_eq_mathlibTilt : FractionField Ω p =
    Tilt Ω (NormedField.valuation (K := Ω)) (LocalGeometricFontaine.integerRing Ω)
      (Valuation.integer.integers _) p := rfl

/-- The carrier and all its proved structures are constructed together. -/
structure Data (R : Type u) [CommRing R] (q : ℕ) where
  Carrier : Type u
  field : Field Carrier
  charP : letI := field
    CharP Carrier q
  perfect : letI := field
    PerfectRing Carrier q
  sourceValuation : Valuation R ℝ≥0
  valuation : letI := field
    Valuation Carrier ℝ≥0
  inclusion : letI := field
    R →+* Carrier
  inclusion_injective : letI := field
    Function.Injective inclusion
  valuation_inclusion : letI := field
    ∀ x, valuation (inclusion x) = sourceValuation x

/-- No field, characteristic, perfection or valuation certificate is supplied by a caller. -/
def ofField : Data (Source Ω p) p where
  Carrier := FractionField Ω p
  field := inferInstance
  charP := inferInstance
  perfect := inferInstance
  sourceValuation := sourceValuation Ω p
  valuation := fractionValuation Ω p
  inclusion := algebraMap (Source Ω p) (FractionField Ω p)
  inclusion_injective := IsFractionRing.injective _ _
  valuation_inclusion := fractionValuation_inclusion Ω p

end
end JoshiTeich.Act1Scene1.GeometricTiltField
