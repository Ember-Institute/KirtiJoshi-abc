import ArithmeticTeichmullerSpaces.Act1Scene1.PrimeAdicSeparation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamLogarithm

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-EMBEDDING
source: Joshi II principal Fontaine kernel (838, 932), Tate period
(935--958) and the B_dR inclusion (1069--1076); Mathlib Witt separation.
fidelity: proves actual Ainf and Ainf[1/p] are separated for the original
Fontaine kernel. Constructs injectivity of the original maps into the
original B_dR+; thus the original nontrivial Tate tower has a nonzero
convergent logarithm there. No separatedness or injectivity certificate
is supplied as an input. Additivity, Frobenius-p and B/rho identities remain
separate obligations. Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamEmbedding

open JoshiTeich.Prologue InitialThetaTiltFontaine
open InitialThetaCanonicalGeometricFontaine
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ < 1) := primeNormFact D w

theorem primitive_constantCoeff :
    (primitive D w).coeff 0 = integralLift D w (Arithmetic.residueChar w.1) := by
  have hp : (Arithmetic.residueChar w.1 : InitialThetaTiltIntegers.Integers D w) = 0 :=
    CharP.cast_eq_zero _ _
  change WittVector.constantCoeff (primitive D w) = _
  rw [primitive, map_sub, map_natCast, hp, sub_zero]
  rfl

theorem primitive_constantCoeff_norm_lt_one : ‖(primitive D w).coeff 0‖ < 1 := by
  rw [primitive_constantCoeff, integralLift_norm]
  exact (primeNormFact D w).out.2

theorem primitive_not_dvd_prime : ¬ primitive D w ∣ (Arithmetic.residueChar w.1 : Ainf D w) := by
  intro h
  have hz := (InitialThetaFontaineKernel.mem_kernel_iff_dvd D w _).mpr h
  rw [map_natCast] at hz
  exact (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero) hz

/-- Infinite divisibility by the actual primitive forces the actual zeroth Witt digit to vanish. -/
theorem constantCoeff_eq_zero_of_all_primitive_pow_dvd (a : Ainf D w)
    (ha : ∀ n : ℕ, primitive D w ^ n ∣ a) : a.coeff 0 = 0 := by
  have hbound (n : ℕ) : ‖a.coeff 0‖ ≤ ‖(primitive D w).coeff 0‖ ^ n := by
    obtain ⟨b, hb⟩ := ha n
    have he : a.coeff 0 = (primitive D w).coeff 0 ^ n * b.coeff 0 := by
      change WittVector.constantCoeff a =
        WittVector.constantCoeff (primitive D w) ^ n * WittVector.constantCoeff b
      rw [hb, map_mul, map_pow]
    rw [he, norm_mul, norm_pow]
    apply mul_le_of_le_one_right (by positivity)
    exact (LocalGeometricFontaine.mem_integerRing _ _).mp (b.coeff 0).property
  have hz : ‖a.coeff 0‖ ≤ 0 :=
    ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (primitive_constantCoeff_norm_lt_one D w)) (Filter.Eventually.of_forall hbound)
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))

/-- This is proved in the original Witt carrier, before any localization or completion. -/
instance primitiveSeparated : IsHausdorff (Ideal.span {primitive D w}) (Ainf D w) := by
  apply PrimeAdicSeparation.of_mod_p (Arithmetic.residueChar w.1 : Ainf D w) (primitive D w)
    (InitialThetaFontaineKernel.primitive_prime D w) (primitive_not_dvd_prime D w)
  intro a ha
  apply Ideal.mem_span_singleton.mp
  exact (WittVector.mem_span_p_iff_coeff_zero_eq_zero a).mpr
    (constantCoeff_eq_zero_of_all_primitive_pow_dvd D w a ha)

instance localizedKernelSeparated : IsHausdorff
    (RingHom.ker (InitialThetaFontaineLocalization.theta D w))
    (InitialThetaFontaineLocalization.AinfInvertP D w) := by
  rw [InitialThetaFontaineLocalization.kernel_eq_span]
  exact PrimeAdicSeparation.away (InitialThetaFontaineLocalization.AinfInvertP D w)
    (Arithmetic.residueChar w.1 : Ainf D w) (primitive D w)
    (InitialThetaFontaineLocalization.prime_ne_zero D w)
    (InitialThetaFontaineKernel.primitive_prime D w) (primitive_not_dvd_prime D w)

instance sourceKernelSeparated : IsHausdorff (InitialThetaDeRhamCompletion.sourceKernel D w)
    (InitialThetaDeRhamCompletion.Source D w) := by
  let I := RingHom.ker (InitialThetaFontaineLocalization.theta D w)
  let e := (InitialThetaFontaineLocalization.sourceLocalizationEquiv D w).symm
  have hm : I.map e = InitialThetaDeRhamCompletion.sourceKernel D w := by
    dsimp only [I]
    rw [InitialThetaFontaineLocalization.kernel_eq_span, Ideal.map_span, Set.image_singleton]
    exact (InitialThetaDeRhamCompletion.sourceKernel_eq_span D w).symm
  have h := (IsHausdorff.congr_ringEquiv I e).mpr (localizedKernelSeparated D w)
  rw [hm] at h
  exact h

theorem sourceToPlus_injective : Function.Injective
    (AdicCompletion.of (InitialThetaDeRhamCompletion.sourceKernel D w)
      (InitialThetaDeRhamCompletion.Source D w)) :=
  AdicCompletion.of_injective (InitialThetaDeRhamCompletion.sourceKernel D w)
    (InitialThetaDeRhamCompletion.Source D w)

theorem localizationToPlus_injective :
    Function.Injective (InitialThetaDeRhamTeichmuller.localizationToPlus D w) :=
  (sourceToPlus_injective D w).comp
    (InitialThetaFontaineLocalization.sourceLocalizationEquiv D w).symm.injective

theorem ainfToPlus_injective : Function.Injective (InitialThetaDeRhamTeichmuller.ainfToPlus D w) :=
  (localizationToPlus_injective D w).comp (InitialThetaFontaineLocalization.algebraMap_injective D w)

theorem tateCoordinate_injective : Function.Injective (InitialThetaDeRhamLogarithm.tateCoordinate D w) :=
  (ainfToPlus_injective D w).comp (InitialThetaCyclotomicTateTilt.kernelCoordinate_injective D w)

theorem tateCoordinate_one : InitialThetaDeRhamLogarithm.tateCoordinate D w 1 = 0 := by
  rw [InitialThetaDeRhamLogarithm.tateCoordinate,
    InitialThetaCyclotomicTateTilt.kernelCoordinate_one, map_zero]

/-- No nontrivial original Tate tower is killed by completion or the convergent logarithm. -/
theorem tateLog_eq_zero_iff (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    InitialThetaDeRhamLogarithm.tateLog D w x = 0 ↔ x = 1 := by
  rw [InitialThetaDeRhamLogarithm.tateLog_eq_zero_iff, ← tateCoordinate_one D w]
  exact (tateCoordinate_injective D w).eq_iff

def canonicalTateLog : InitialThetaDeRhamCompletion.Ring D w :=
  InitialThetaDeRhamLogarithm.tateLog D w (InitialThetaCyclotomicTateTilt.generator D w)

theorem canonicalTateLog_ne_zero : canonicalTateLog D w ≠ 0 := by
  intro h
  exact InitialThetaCyclotomicTateTilt.generator_ne_one D w
    ((tateLog_eq_zero_iff D w _).mp h)

theorem theta_canonicalTateLog :
    InitialThetaDeRhamCompletion.theta D w (canonicalTateLog D w) = 0 :=
  InitialThetaDeRhamLogarithm.theta_tateLog D w _

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamEmbedding
