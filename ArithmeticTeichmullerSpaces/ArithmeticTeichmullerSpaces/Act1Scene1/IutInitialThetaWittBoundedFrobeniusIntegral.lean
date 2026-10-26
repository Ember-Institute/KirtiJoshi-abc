import ArithmeticTeichmullerSpaces.Act1Scene1.WittFractionFrobeniusRigidity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTeichmullerRecognition

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-BOUNDED-FROBENIUS-INTEGRAL
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, bounded
Witt localization and Teichmuller representatives of periods.
fidelity: for an actual bounded localization element satisfying
phi(x)=x^p, removes its proved p-power numerator denominator and gives
an actual tilt Teichmuller representative in Frac(W(F)). Its original
rho norm equals that coefficient's norm. A bound at any one radius
therefore makes the same element an image of original Ainf.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; completed elements still require an actual
bounded source representative. No source-surjectivity law is input.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittBoundedFrobeniusIntegral

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaBoundedWittExpansion InitialThetaWittRhoFrobenius
open InitialThetaWittRhoFrobeniusCompletion InitialThetaWittRhoFrobeniusEquiv
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_ambient_teichmuller (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : InitialThetaBoundedWittLocalization.frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1) :
    ∃ r : InitialThetaTiltField.Carrier D w,
      algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller (Arithmetic.residueChar w.1) r) =
        toAmbient D w x := by
  let P := InitialThetaWittRhoValue.presentation D w x
  apply WittFractionFrobeniusRigidity.exists_teichmuller_of_prime_presentation
    (Arithmetic.residueChar w.1) (toAmbient D w x) _ P.exponent P.numerator P.relation
  change ambientFrobenius D w (toAmbient D w x) = _
  rw [← toAmbient_frobenius, hx, map_pow]

theorem realValue_eq_norm_of_teichmuller (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w)
    (r : InitialThetaTiltField.Carrier D w)
    (hr : algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller (Arithmetic.residueChar w.1) r) =
      toAmbient D w x) : InitialThetaWittRhoNorm.realValue D w ρ.val x = ‖r‖ := by
  have hpres : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ 0 =
      algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller (Arithmetic.residueChar w.1) r) := by
    simpa only [pow_zero, mul_one] using hr.symm
  rw [InitialThetaWittRhoNorm.realValue, InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val
    ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne x 0 _ hpres]
  simp only [pow_zero, div_one, WittWeightedDigits.value_teichmuller, ENNReal.toReal_ofReal (norm_nonneg r)]

theorem exists_integral_of_source_equation (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : InitialThetaBoundedWittLocalization.frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1)
    (hn : InitialThetaWittRhoNorm.realValue D w ρ.val x ≤ 1) :
    ∃ a : InitialThetaTiltFontaine.Ainf D w, InitialThetaBoundedWittLocalization.inclusion D w a = x := by
  obtain ⟨r, hr⟩ := exists_ambient_teichmuller D w x hx
  have hnr : ‖r‖ ≤ 1 := by rwa [realValue_eq_norm_of_teichmuller D w ρ x r hr] at hn
  let r' : InitialThetaTiltIntegers.Integers D w := ⟨r, (LocalGeometricFontaine.mem_integerRing _ _).mpr hnr⟩
  refine ⟨WittVector.teichmuller (Arithmetic.residueChar w.1) r', ?_⟩
  apply toAmbient_injective D w
  rw [toAmbient_inclusion]
  change algebraMap (FieldWitt D w) (Ambient D w)
    (WittVector.map (algebraMap (InitialThetaTiltIntegers.Integers D w) (InitialThetaTiltField.Carrier D w))
      (WittVector.teichmuller (Arithmetic.residueChar w.1) r')) = _
  rw [WittVector.map_teichmuller]
  exact hr

theorem source_equation_of_completed (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : completedEquiv D w ρ (InitialThetaWittRhoCompletion.inclusion D w ρ x) =
      InitialThetaWittRhoCompletion.inclusion D w (poweredRadius D w ρ) x ^ Arithmetic.residueChar w.1) :
    InitialThetaBoundedWittLocalization.frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1 := by
  apply InitialThetaWittRhoCompletion.inclusion_injective D w (poweredRadius D w ρ)
  rw [map_pow]
  exact (completedEquiv_inclusion D w ρ x).symm.trans hx

end
end JoshiTeich.Act1Scene1.InitialThetaWittBoundedFrobeniusIntegral
