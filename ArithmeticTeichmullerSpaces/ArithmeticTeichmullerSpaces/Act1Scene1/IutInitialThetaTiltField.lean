import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltField
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalGeometricFontaine

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-FIELD
source: Joshi I def:arith-hol-strs; Arithmetic Holomorphic Structures tilt
following lem:perfectoid; Mathlib Tilt and PreTilt valuation.
fidelity: for the same actual InitialThetaData supported place, constructs
the algebraic tilt from the previously constructed geometric coefficient
field. Its field, characteristic p, perfectness, inclusion and valuation
are proved producers. No external tilt field or Frobenius/valuation law is
input. Tilt topology/completeness and a selected holomorphoid identity remain
open. Original proofs; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltField

open JoshiTeich.Prologue
open scoped NNReal
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Source := PreTilt
  (LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
  (Arithmetic.residueChar w.1)

/-- Actual pretilt and fraction-field data from this same completion coefficient field. -/
def data :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    GeometricTiltField.Data (Source D w) (Arithmetic.residueChar w.1) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact GeometricTiltField.ofField
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1)

def Carrier : Type u := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).Carrier

instance carrierField : Field (Carrier D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).field

instance carrierCharP : CharP (Carrier D w) (Arithmetic.residueChar w.1) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).charP

instance carrierPerfect : PerfectRing (Carrier D w) (Arithmetic.residueChar w.1) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).perfect

def inclusion :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    Source D w →+* Carrier D w := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).inclusion

theorem inclusion_injective :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    Function.Injective (inclusion D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).inclusion_injective

def sourceValuation :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    Valuation (Source D w) ℝ≥0 := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).sourceValuation

def valuation : Valuation (Carrier D w) ℝ≥0 := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).valuation

theorem sourceValuation_eq :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    sourceValuation D w = GeometricTiltField.sourceValuation
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rfl

theorem valuation_inclusion (x : Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    valuation D w (inclusion D w x) = sourceValuation D w x := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).valuation_inclusion x

theorem valuation_div (a b : Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    valuation D w (inclusion D w a / inclusion D w b) =
      sourceValuation D w a / sourceValuation D w b := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [map_div₀, valuation_inclusion, valuation_inclusion]

theorem valuation_eq_zero_iff (x : Carrier D w) : valuation D w x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hh : (0 : ℝ≥0) = 1 := calc
      0 = valuation D w x * valuation D w x⁻¹ := by rw [h, zero_mul]
      _ = valuation D w (x * x⁻¹) := (map_mul (valuation D w) x x⁻¹).symm
      _ = 1 := by rw [mul_inv_cancel₀ hx, map_one]
    exact zero_ne_one hh
  · rintro rfl
    exact map_zero _

theorem frobenius_bijective :
    Function.Bijective (frobenius (Carrier D w) (Arithmetic.residueChar w.1)) :=
  bijective_frobenius _ _

theorem inclusion_frobenius (x : Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    frobenius (Carrier D w) (Arithmetic.residueChar w.1) (inclusion D w x) =
      inclusion D w (frobenius (Source D w) (Arithmetic.residueChar w.1) x) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  simp only [frobenius_def, map_pow]

theorem valuation_frobenius (x : Carrier D w) :
    valuation D w (frobenius (Carrier D w) (Arithmetic.residueChar w.1) x) =
      valuation D w x ^ Arithmetic.residueChar w.1 := by
  rw [frobenius_def, map_pow]

theorem valuation_inverseFrobenius_pow (x : Carrier D w) :
    valuation D w ((frobeniusEquiv (Carrier D w) (Arithmetic.residueChar w.1)).symm x) ^
        Arithmetic.residueChar w.1 = valuation D w x := by
  rw [← map_pow]
  exact congrArg (valuation D w)
    ((frobeniusEquiv (Carrier D w) (Arithmetic.residueChar w.1)).apply_symm_apply x)

end
end JoshiTeich.Act1Scene1.InitialThetaTiltField
