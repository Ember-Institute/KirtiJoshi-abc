import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalPrimeDivision
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalPeriodKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RATIONAL-TATE-PRINCIPAL-LIFT
source: Joshi II `eq:tate-module-of-lubin-tate` and the period sequence
in the proof of `pr:teichmuller-lift-A`.
fidelity: clears the p-power denominator of each actual rational Tate
coefficient, uses the original integral Tate scalar action, and then
takes the actual inverse-Frobenius principal-unit root. Its logarithm
is the prescribed rational Tate period. Combined with the proved kernel
classification, the rational Tate line equals the intersection of the
actual principal logarithm image with the theta kernel.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the full phi=p space is unchanged. Its equality
with the principal logarithm image is not assumed or asserted. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRationalTatePrincipalLift

open JoshiTeich.Prologue InitialThetaWittPrincipalUnitDomain
open InitialThetaWittPrincipalUnitPeriod InitialThetaWittPrincipalPrimeDivision
open InitialThetaWittTateLogarithm InitialThetaWittAdditiveTatePeriod
open InitialThetaWittTateLogarithmLinear InitialThetaWittRationalTateSource
open InitialThetaWittRationalTatePeriod InitialThetaWittPrincipalPeriodKernel
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_integral_scalar (a : Padic (Arithmetic.residueChar w.1)) :
    ∃ k : ℕ, ∃ b : PadicInt (Arithmetic.residueChar w.1),
      (b : Padic (Arithmetic.residueChar w.1)) =
        (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k * a := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (norm_nonneg (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)))
    (Padic.norm_p_lt_one (p := Arithmetic.residueChar w.1))).mul_const ‖a‖
  have ht : Filter.Tendsto (fun k : ℕ =>
      ‖(Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1))‖ ^ k * ‖a‖)
      Filter.atTop (𝓝 0) := by simpa only [zero_mul] using h
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))).exists
  refine ⟨k, ⟨(Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k * a, ?_⟩, rfl⟩
  simpa only [norm_mul, norm_pow] using hk.le

theorem exists_principal_period (v : RationalTate D w) :
    ∃ u : Principal D w, periodLog D w u = periodMap D w v := by
  obtain ⟨k, b, hb⟩ := exists_integral_scalar D w (coefficientEquiv D w v)
  let t : Tate D w := (b • Additive.ofMul (InitialThetaCyclotomicTateTilt.generator D w)).toMul
  have ht : tateLog D w t = (b : Padic (Arithmetic.residueChar w.1)) •
      tateLog D w (InitialThetaCyclotomicTateTilt.generator D w) := by
    have h := tateLogHom_padic_smul D w b
      (Additive.ofMul (InitialThetaCyclotomicTateTilt.generator D w))
    change tateLog D w (b • Additive.ofMul (InitialThetaCyclotomicTateTilt.generator D w)).toMul =
      (b : Padic (Arithmetic.residueChar w.1)) •
        tateLog D w (Additive.ofMul (InitialThetaCyclotomicTateTilt.generator D w)).toMul at h
    simpa only [t, toMul_ofMul] using h
  have hp : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k ≠ 0 :=
    pow_ne_zero k (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  refine ⟨primeRoot D w k (tatePrincipal D w t), ?_⟩
  rw [periodLog_primeRoot, periodLog_tatePrincipal, ht, hb, mul_smul, inv_smul_smul₀ hp]
  exact (periodMap_apply D w v).symm

theorem exists_eigenPrincipalPeriod (v : RationalTate D w) :
    ∃ u : Principal D w, eigenLogHom D w (Additive.ofMul u) = eigenPeriodMap D w v := by
  obtain ⟨u, hu⟩ := exists_principal_period D w v
  exact ⟨u, Subtype.ext hu⟩

def rationalPrincipal (v : RationalTate D w) : Principal D w :=
  Classical.choose (exists_principal_period D w v)

theorem periodLog_rationalPrincipal (v : RationalTate D w) :
    periodLog D w (rationalPrincipal D w v) = periodMap D w v :=
  Classical.choose_spec (exists_principal_period D w v)

theorem periodLogHom_rationalPrincipal (v : RationalTate D w) :
    periodLogHom D w (Additive.ofMul (rationalPrincipal D w v)) = periodMap D w v := by
  change periodLog D w (Additive.ofMul (rationalPrincipal D w v)).toMul = _
  simpa only [toMul_ofMul] using periodLog_rationalPrincipal D w v

def rationalPrincipalHom : RationalTate D w →+ Additive (Principal D w) where
  toFun v := Additive.ofMul (rationalPrincipal D w v)
  map_zero' := by
    apply InitialThetaWittPrincipalUnitInjective.periodLogHom_injective D w
    rw [periodLogHom_rationalPrincipal, map_zero, map_zero]
  map_add' v z := by
    apply InitialThetaWittPrincipalUnitInjective.periodLogHom_injective D w
    rw [map_add, periodLogHom_rationalPrincipal, periodLogHom_rationalPrincipal,
      periodLogHom_rationalPrincipal, map_add]

theorem periodLogHom_rationalPrincipalHom (v : RationalTate D w) :
    periodLogHom D w (rationalPrincipalHom D w v) = periodMap D w v :=
  periodLogHom_rationalPrincipal D w v

theorem rationalPrincipalHom_injective : Function.Injective (rationalPrincipalHom D w) := by
  intro v z h
  apply periodMap_injective D w
  simpa only [periodLogHom_rationalPrincipalHom] using congrArg (periodLogHom D w) h

theorem principalRange_inter_kernel :
    Set.range (periodLog D w) ∩ {x | InitialThetaWittThetaEvaluation.evaluation D w x = 0} =
      ((periodMap D w).range : Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) := by
  ext x
  constructor
  · rintro ⟨⟨u, rfl⟩, hu⟩
    exact periodLog_mem_periodRange_of_evaluation_eq_zero D w u hu
  · intro hx
    obtain ⟨v, hv⟩ := hx
    obtain ⟨u, hu⟩ := exists_principal_period D w v
    refine ⟨⟨u, hu.trans hv⟩, ?_⟩
    exact (InitialThetaWittThetaPadicQuotient.mem_kernelSubmodule D w x).mp
      (periodMap_range_le_kernel D w ⟨v, hv⟩)

end
end JoshiTeich.Act1Scene1.InitialThetaWittRationalTatePrincipalLift
