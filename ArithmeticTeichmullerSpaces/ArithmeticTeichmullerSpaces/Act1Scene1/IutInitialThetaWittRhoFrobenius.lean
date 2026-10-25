import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoNorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-FROBENIUS
source: Joshi II `se:ff-rings`, Frobenius and the family of rho norms.
fidelity: transports the actual Witt Frobenius through the fraction
field and the bounded localization. A common numerator presentation
proves the exact radius-power identity without a supplied norm law.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; completion transport is separate. No scalar
algebra, multiplicative norm equality or paper B/BK identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoFrobenius

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion InitialThetaBoundedWittLocalization
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def fieldFrobenius : FieldWitt D w ≃+* FieldWitt D w :=
  WittVector.frobeniusEquiv (Arithmetic.residueChar w.1) (InitialThetaTiltField.Carrier D w)

def ambientFrobenius : Ambient D w ≃+* Ambient D w :=
  IsFractionRing.ringEquivOfRingEquiv (fieldFrobenius D w)

theorem ambientFrobenius_algebraMap (a : FieldWitt D w) :
    ambientFrobenius D w (algebraMap (FieldWitt D w) (Ambient D w) a) =
      algebraMap (FieldWitt D w) (Ambient D w) (fieldFrobenius D w a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem wittInclusion_frobenius (a : InitialThetaTiltFontaine.Ainf D w) :
    wittInclusion D w (sourceFrobenius D w a) = fieldFrobenius D w (wittInclusion D w a) := by
  apply WittVector.ext
  intro n
  change (WittVector.map _ (WittVector.frobenius a)).coeff n =
    (WittVector.frobenius (WittVector.map _ a)).coeff n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

theorem toAmbient_frobenius (x : InitialThetaBoundedWittLocalization.Ring D w) :
    toAmbient D w (frobeniusEquiv D w x) = ambientFrobenius D w (toAmbient D w x) := by
  have he : (toAmbient D w).comp (frobeniusEquiv D w).toRingHom =
      (ambientFrobenius D w).toRingHom.comp (toAmbient D w) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator D w))
    ext a
    change toAmbient D w (frobenius D w (inclusion D w a)) =
      ambientFrobenius D w (toAmbient D w (inclusion D w a))
    rw [frobenius_inclusion, toAmbient_inclusion, toAmbient_inclusion]
    change algebraMap (FieldWitt D w) (Ambient D w) (wittInclusion D w (sourceFrobenius D w a)) =
      ambientFrobenius D w (algebraMap (FieldWitt D w) (Ambient D w) (wittInclusion D w a))
    rw [ambientFrobenius_algebraMap, wittInclusion_frobenius]
  exact RingHom.congr_fun he x

theorem frobenius_presentation (x : InitialThetaBoundedWittLocalization.Ring D w)
    (P : InitialThetaWittRhoValue.Presentation D w x) :
    toAmbient D w (frobeniusEquiv D w x) * (Arithmetic.residueChar w.1 : Ambient D w) ^ P.exponent =
      algebraMap (FieldWitt D w) (Ambient D w) (fieldFrobenius D w P.numerator) := by
  have h := congrArg (ambientFrobenius D w) P.relation
  simpa only [map_mul, map_pow, map_natCast, ambientFrobenius_algebraMap,
    ← toAmbient_frobenius] using h

theorem value_frobenius (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoValue.value D w (ρ ^ Arithmetic.residueChar w.1) (frobeniusEquiv D w x) =
      InitialThetaWittRhoValue.value D w ρ x ^ Arithmetic.residueChar w.1 := by
  let P := InitialThetaWittRhoValue.presentation D w x
  rw [InitialThetaWittRhoValue.value_eq_of_presentation D w _
    (pow_ne_zero _ hρ0) (ENNReal.pow_ne_top hρtop) _ P.exponent _ (frobenius_presentation D w x P),
    InitialThetaWittRhoValue.value_eq_of_presentation D w ρ hρ0 hρtop x P.exponent P.numerator P.relation]
  change WittWeightedDigits.value _ _ (WittVector.frobenius P.numerator) / _ = _
  rw [WittWeightedDigitFrobenius.value_frobenius]
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem realValue_frobenius (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoNorm.realValue D w (ρ ^ Arithmetic.residueChar w.1) (frobeniusEquiv D w x) =
      InitialThetaWittRhoNorm.realValue D w ρ x ^ Arithmetic.residueChar w.1 := by
  simp only [InitialThetaWittRhoNorm.realValue, value_frobenius D w ρ hρ0 hρtop,
    ENNReal.toReal_pow]

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoFrobenius
