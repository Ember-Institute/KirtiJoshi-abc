import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTwistedIntegralRecognition
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAmbientFixedScalars
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateBanachQuotientFullKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FULL-TATE-KERNEL
source: Joshi II `eq:tate-module-of-lubin-tate` and the displayed
exact sequence in the proof of `pr:teichmuller-lift-A` (935--958),
citing Fargues--Fontaine Proposition 4.5.14.
fidelity: constructs bounded source representatives of all original
full common-ring twisted solutions using the proved integral producer
and actual Q_p scaling. The ratio of two nonzero source solutions is
fixed in the original Witt fraction field and hence is an existing
actual Q_p scalar. Injective source maps transport the comparison back
to the original common ring. This proves unique scalar classification,
surjectivity of the actual twisted Tate period map, the full actual
theta-kernel identity and injectivity of the actual Tate Banach quotient
evaluation. No classification, source lift or kernel law is an input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; all original elements, scalar actions and
topologies are retained. Identification with paper B, global holomorphoid
markings and H1e/BK comparison remain separate. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFullTateKernel

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittThetaPrincipalKernel InitialThetaWittBoundedThetaPrincipal
open InitialThetaBoundedWittExpansion InitialThetaBoundedWittPadicScalars
open InitialThetaWittRhoFrobenius InitialThetaWittEigenKernelTwistedComparison
open InitialThetaWittTwistedTatePeriod
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

private theorem exists_bounded_twisted (x : InitialThetaWittAllRadiusCompletion.Carrier D w)
    (hx : InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x = -primitive D w * x) :
    ∃ a : InitialThetaBoundedWittLocalization.Ring D w,
      inclusion D w a = x ∧
        InitialThetaBoundedWittLocalization.frobeniusEquiv D w a = -boundedPrimitive D w * a := by
  obtain ⟨N, a, ha, _⟩ := InitialThetaWittTwistedIntegralRecognition.exists_integral_prime_pow D w x hx
  let c : Padic (Arithmetic.residueChar w.1) := (Arithmetic.residueChar w.1 : Padic _) ^ N
  have hc : c ≠ 0 := pow_ne_zero N (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  have ha' : inclusion D w (InitialThetaBoundedWittLocalization.inclusion D w a) = c • x := by
    change InitialThetaWittAllRadiusExpansion.ainfMap D w a = c • x
    simpa only [c, Algebra.smul_def, map_pow, map_natCast] using ha
  let b : InitialThetaBoundedWittLocalization.Ring D w :=
    c⁻¹ • InitialThetaBoundedWittLocalization.inclusion D w a
  have hb : inclusion D w b = x := by
    change inclusion D w (c⁻¹ • InitialThetaBoundedWittLocalization.inclusion D w a) = x
    rw [inclusion_smul, ha', inv_smul_smul₀ hc]
  refine ⟨b, hb, ?_⟩
  apply inclusion_injective D w
  rw [← InitialThetaWittAllRadiusFrobenius.frobenius_inclusion,
    map_mul, map_neg, inclusion_boundedPrimitive, hb, hx]

private theorem source_scalar_comparison
    (a b : InitialThetaBoundedWittLocalization.Ring D w) (hb : b ≠ 0)
    (haeq : InitialThetaBoundedWittLocalization.frobeniusEquiv D w a = -boundedPrimitive D w * a)
    (hbeq : InitialThetaBoundedWittLocalization.frobeniusEquiv D w b = -boundedPrimitive D w * b) :
    ∃ c : Padic (Arithmetic.residueChar w.1), c • b = a := by
  have hb' : toAmbient D w b ≠ 0 := fun h =>
    hb (toAmbient_injective D w (h.trans (map_zero _).symm))
  have hprim : toAmbient D w (-boundedPrimitive D w) ≠ 0 := by
    intro h
    have hzero : boundedPrimitive D w = 0 := by
      have hn : -boundedPrimitive D w = 0 :=
        toAmbient_injective D w (h.trans (map_zero _).symm)
      exact neg_eq_zero.mp hn
    apply primitive_ne_zero D w
    rw [← inclusion_boundedPrimitive, hzero, map_zero]
  have hfa : ambientFrobenius D w (toAmbient D w a) =
      toAmbient D w (-boundedPrimitive D w) * toAmbient D w a := by
    rw [← toAmbient_frobenius, haeq, map_mul]
  have hfb : ambientFrobenius D w (toAmbient D w b) =
      toAmbient D w (-boundedPrimitive D w) * toAmbient D w b := by
    rw [← toAmbient_frobenius, hbeq, map_mul]
  have hfixed : ambientFrobenius D w (toAmbient D w a / toAmbient D w b) =
      toAmbient D w a / toAmbient D w b := by
    rw [map_div₀, hfa, hfb, mul_div_mul_left _ _ hprim]
  obtain ⟨c, hc⟩ := (InitialThetaWittAmbientFixedScalars.ambientFrobenius_eq_self_iff D w _).mp hfixed
  refine ⟨c, ?_⟩
  apply toAmbient_injective D w
  change toAmbient D w (padicMap D w c * b) = _
  rw [map_mul, hc, div_mul_cancel₀ _ hb']

theorem existsUnique_scalar_of_twisted
    (x y : InitialThetaWittAllRadiusCompletion.Carrier D w) (hy : y ≠ 0)
    (hx : InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x = -primitive D w * x)
    (hyeq : InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w y = -primitive D w * y) :
    ∃! c : Padic (Arithmetic.residueChar w.1), c • y = x := by
  obtain ⟨a, ha, haeq⟩ := exists_bounded_twisted D w x hx
  obtain ⟨b, hb, hbeq⟩ := exists_bounded_twisted D w y hyeq
  have hb0 : b ≠ 0 := by
    intro h
    exact hy (hb.symm.trans (by rw [h, map_zero]))
  obtain ⟨c, hc⟩ := source_scalar_comparison D w a b hb0 haeq hbeq
  have hc' : c • y = x := by
    rw [← hb, ← inclusion_smul, hc, ha]
  refine ⟨c, hc', ?_⟩
  intro d hd
  exact smul_left_injective (Padic (Arithmetic.residueChar w.1)) hy (hd.trans hc'.symm)

theorem unique_scalar_representation (y : twistedSubmodule D w) :
    ∃! c : Padic (Arithmetic.residueChar w.1), c • canonicalSolution D w = y := by
  have hne : (canonicalSolution D w).val ≠ 0 := by
    intro h
    exact canonicalSolution_ne_zero D w (Subtype.ext h)
  obtain ⟨c, hc, huniq⟩ := existsUnique_scalar_of_twisted D w y.val
    (canonicalSolution D w).val hne ((mem_twisted_iff D w _).mp y.property)
    (canonicalSolution_equation D w)
  refine ⟨c, Subtype.ext hc, ?_⟩
  intro d hd
  exact huniq d (congrArg Subtype.val hd)

theorem twistedPeriodMap_surjective : Function.Surjective (twistedPeriodMap D w) :=
  (unique_scalar_representation_iff_surjective D w).mp (unique_scalar_representation D w)

theorem fullKernel_eq_periodRange :
    fullKernel D w = (InitialThetaWittRationalTatePeriod.periodMap D w).range :=
  (fullKernel_eq_periodRange_iff_surjective D w).mpr (twistedPeriodMap_surjective D w)

theorem quotientEvaluation_injective :
    Function.Injective (InitialThetaWittTateBanachQuotient.quotientEvaluation D w) :=
  (InitialThetaWittTateBanachQuotientFullKernel.quotientEvaluation_injective_iff_fullKernel_eq_periodMapRange
    D w).mpr (fullKernel_eq_periodRange D w)

end
end JoshiTeich.Act1Scene1.InitialThetaWittFullTateKernel
