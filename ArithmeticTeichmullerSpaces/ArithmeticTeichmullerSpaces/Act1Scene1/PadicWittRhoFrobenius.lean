import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoValue
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusTeichmullerRigidity

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-FROBENIUS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`.
fidelity: transports the original Witt Frobenius and its inverse through
the standard p-only Away localization, then proves the rho value power law
from a common numerator presentation.
boundary: does not extend Frobenius to fixed-radius completions or the
all-radius carrier, and does not claim the paper B identity.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius

open PadicBoundedWittExpansion PadicBoundedWittLocalization
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

local instance coefficientField : Field (PadicTiltField.Carrier p) :=
  FractionRing.field (PadicTiltField.Source p)

private def coefficientInclusion : PadicTiltField.Integers p →+*
    PadicTiltField.Carrier p where
  toFun := Subtype.val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

local instance integersPerfect : PerfectRing (PadicTiltField.Integers p) p := by
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius
    (R := PadicTiltField.Carrier p) (p := p)).surjective
      (x : PadicTiltField.Carrier p)
  change y ^ p = (x : PadicTiltField.Carrier p) at hy
  have hnorm : ‖y‖ ^ p ≤ 1 := by
    rw [← norm_pow, hy]
    exact (LocalGeometricFontaine.mem_integerRing _ _).mp x.property
  let z : PadicTiltField.Integers p := ⟨y,
    (LocalGeometricFontaine.mem_integerRing _ _).mpr
      ((pow_le_one_iff_of_nonneg (norm_nonneg y) (Fact.out : p.Prime).ne_zero).mp hnorm)⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change y ^ p = (x : PadicTiltField.Carrier p)
  exact hy

def sourceFrobenius : Ainf p ≃+* Ainf p :=
  WittVector.frobeniusEquiv p (PadicTiltField.Integers p)

theorem sourceFrobenius_teich :
    sourceFrobenius p (teich p) = teich p ^ p := by
  change WittVector.frobenius (WittVector.teichmuller p (contraction p)) = _
  exact WittFrobeniusTeichmullerRigidity.frobenius_teichmuller p _

theorem inverseFrobenius_teich_pow :
    ((sourceFrobenius p).symm (teich p)) ^ p = teich p := by
  apply (sourceFrobenius p).injective
  rw [map_pow, RingEquiv.apply_symm_apply, sourceFrobenius_teich]

theorem frobenius_denominator_isUnit : IsUnit
    ((inclusion p).comp (sourceFrobenius p).toRingHom (denominator p)) := by
  change IsUnit (inclusion p (sourceFrobenius p
    ((p : Ainf p) * teich p)))
  rw [map_mul, map_natCast, sourceFrobenius_teich, map_mul, map_pow]
  exact (prime_isUnit p).mul ((teich_isUnit p).pow _)

theorem inverseFrobenius_denominator_isUnit : IsUnit
    ((inclusion p).comp (sourceFrobenius p).symm.toRingHom (denominator p)) := by
  have ht : IsUnit (inclusion p ((sourceFrobenius p).symm (teich p))) := by
    apply isUnit_of_dvd_unit (dvd_pow_self _ (Fact.out : p.Prime).ne_zero)
    rw [← map_pow, inverseFrobenius_teich_pow]
    exact teich_isUnit p
  change IsUnit (inclusion p ((sourceFrobenius p).symm
    ((p : Ainf p) * teich p)))
  rw [map_mul, map_natCast, map_mul]
  exact (prime_isUnit p).mul ht

def frobenius : Ring p →+* Ring p :=
  IsLocalization.Away.lift (denominator p) (frobenius_denominator_isUnit p)

def inverseFrobenius : Ring p →+* Ring p :=
  IsLocalization.Away.lift (denominator p) (inverseFrobenius_denominator_isUnit p)

theorem frobenius_inclusion (a : Ainf p) :
    frobenius p (inclusion p a) = inclusion p (sourceFrobenius p a) :=
  IsLocalization.Away.lift_eq _ _ a

theorem inverseFrobenius_inclusion (a : Ainf p) :
    inverseFrobenius p (inclusion p a) = inclusion p ((sourceFrobenius p).symm a) :=
  IsLocalization.Away.lift_eq _ _ a

def frobeniusEquiv : Ring p ≃+* Ring p where
  __ := frobenius p
  invFun := inverseFrobenius p
  left_inv x := by
    have he : (inverseFrobenius p).comp (frobenius p) = RingHom.id (Ring p) := by
      apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator p))
      ext a
      change inverseFrobenius p (frobenius p (inclusion p a)) = inclusion p a
      rw [frobenius_inclusion, inverseFrobenius_inclusion, RingEquiv.symm_apply_apply]
    exact RingHom.congr_fun he x
  right_inv x := by
    have he : (frobenius p).comp (inverseFrobenius p) = RingHom.id (Ring p) := by
      apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator p))
      ext a
      change frobenius p (inverseFrobenius p (inclusion p a)) = inclusion p a
      rw [inverseFrobenius_inclusion, frobenius_inclusion, RingEquiv.apply_symm_apply]
    exact RingHom.congr_fun he x

def fieldFrobenius : FieldWitt p ≃+* FieldWitt p :=
  WittVector.frobeniusEquiv p (PadicTiltField.Carrier p)

def ambientFrobenius : Ambient p ≃+* Ambient p :=
  IsFractionRing.ringEquivOfRingEquiv (fieldFrobenius p)

theorem ambientFrobenius_algebraMap (a : FieldWitt p) :
    ambientFrobenius p (algebraMap (FieldWitt p) (Ambient p) a) =
      algebraMap (FieldWitt p) (Ambient p) (fieldFrobenius p a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem wittInclusion_frobenius (a : Ainf p) :
    wittInclusion p (sourceFrobenius p a) = fieldFrobenius p (wittInclusion p a) := by
  apply WittVector.ext
  intro n
  change (WittVector.map _ (WittVector.frobenius a)).coeff n =
    (WittVector.frobenius (WittVector.map _ a)).coeff n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

theorem toAmbient_frobenius (x : Ring p) :
    toAmbient p (frobeniusEquiv p x) = ambientFrobenius p (toAmbient p x) := by
  have he : (toAmbient p).comp (frobeniusEquiv p).toRingHom =
      (ambientFrobenius p).toRingHom.comp (toAmbient p) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator p))
    ext a
    change toAmbient p (frobenius p (inclusion p a)) =
      ambientFrobenius p (toAmbient p (inclusion p a))
    rw [frobenius_inclusion, toAmbient_inclusion, toAmbient_inclusion]
    change algebraMap (FieldWitt p) (Ambient p) (wittInclusion p (sourceFrobenius p a)) =
      ambientFrobenius p (algebraMap (FieldWitt p) (Ambient p) (wittInclusion p a))
    rw [ambientFrobenius_algebraMap, wittInclusion_frobenius]
  exact RingHom.congr_fun he x

theorem frobenius_presentation (x : Ring p) (P : PadicWittRhoValue.Presentation p x) :
    toAmbient p (frobeniusEquiv p x) * (p : Ambient p) ^ P.exponent =
      algebraMap (FieldWitt p) (Ambient p) (fieldFrobenius p P.numerator) := by
  have h := congrArg (ambientFrobenius p) P.relation
  simpa only [map_mul, map_pow, map_natCast, ambientFrobenius_algebraMap,
    ← toAmbient_frobenius] using h

theorem value_frobenius (ρ : ℝ≥0∞) (hρ0 : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (x : Ring p) :
    PadicWittRhoValue.value p (ρ ^ p) (frobeniusEquiv p x) =
      PadicWittRhoValue.value p ρ x ^ p := by
  let P := PadicWittRhoValue.presentation p x
  rw [PadicWittRhoValue.value_eq_of_presentation p _
    (pow_ne_zero _ hρ0) (ENNReal.pow_ne_top hρtop) _ P.exponent _
      (frobenius_presentation p x P),
    PadicWittRhoValue.value_eq_of_presentation p ρ hρ0 hρtop x P.exponent P.numerator P.relation]
  change WittWeightedDigits.value p _ (WittVector.frobenius P.numerator) / _ = _
  rw [WittWeightedDigitFrobenius.value_frobenius]
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem realValue_frobenius (ρ : PadicWittRhoCompletion.Radius) (x : Ring p) :
    PadicWittRhoNorm.realValue p (ρ.val ^ p) (frobeniusEquiv p x) =
      PadicWittRhoNorm.realValue p ρ.val x ^ p := by
  simp only [PadicWittRhoNorm.realValue,
    value_frobenius p ρ.val ρ.property.1.ne'
      (ρ.property.2.trans ENNReal.one_lt_top).ne,
    ENNReal.toReal_pow]

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius
