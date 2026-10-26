import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalSharpKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittUntiltLogDetection

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-PERIOD-KERNEL
source: Joshi II `pr:teichmuller-lift-A`, the kernel term T_y tensor Q_p
in the displayed period sequence, using the multiplicative formal group.
fidelity: a principal-unit period with zero theta value has a p-power
whose actual sharp is one. The proved sharp kernel recovers an actual
compatible Tate tower. Its logarithmic period equals that p-power times
the original period, giving an explicit pure tensor with inverse p-power
coefficient. Thus theta-zero is equivalent to membership in the actual
rational Tate period line for every principal-unit period.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; representation of every phi=p element by a
principal-unit logarithm and the full phi=p kernel identity remain open.
No dimension, kernel or representation law is supplied as input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalPeriodKernel

open JoshiTeich.Prologue InitialThetaWittThetaEvaluation
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittPrincipalSharpKernel InitialThetaWittUntiltLogDetection
open InitialThetaWittRationalTatePeriod
open scoped TensorProduct
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_prime_pow_tatePrincipal (u : Principal D w)
    (hu : evaluation D w (periodLog D w u) = 0) :
    ∃ k : ℕ, ∃ t : InitialThetaCyclotomicTateTilt.Tate D w,
      tatePrincipal D w t = u ^ (Arithmetic.residueChar w.1 ^ k) := by
  obtain ⟨k, hk⟩ := exists_prime_pow_untiltCoordinate_eq_zero D w u hu
  obtain ⟨t, ht⟩ := (untiltCoordinate_eq_zero_iff D w _).mp hk
  exact ⟨k, t, ht⟩

theorem periodLog_mem_periodRange_of_evaluation_eq_zero (u : Principal D w)
    (hu : evaluation D w (periodLog D w u) = 0) :
    periodLog D w u ∈ (periodMap D w).range := by
  obtain ⟨k, t, ht⟩ := exists_prime_pow_tatePrincipal D w u hu
  let a : Padic (Arithmetic.residueChar w.1) :=
    (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k
  have ha : a ≠ 0 := pow_ne_zero k
    (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  have hnat : ((Arithmetic.residueChar w.1 ^ k : ℕ) : Padic (Arithmetic.residueChar w.1)) •
      periodLog D w u = InitialThetaWittTateLogarithm.tateLog D w t := by
    rw [Nat.cast_smul_eq_nsmul, ← periodLog_pow, ← ht, periodLog_tatePrincipal]
  have he : a • periodLog D w u = InitialThetaWittTateLogarithm.tateLog D w t := by
    simpa only [a, Nat.cast_pow] using hnat
  refine ⟨a⁻¹ ⊗ₜ Additive.ofMul t, ?_⟩
  change periodMap D w (a⁻¹ ⊗ₜ Additive.ofMul t) = periodLog D w u
  rw [periodMap_tmul, toMul_ofMul, ← he, inv_smul_smul₀ ha]

theorem periodLog_mem_periodRange_iff (u : Principal D w) :
    periodLog D w u ∈ (periodMap D w).range ↔ evaluation D w (periodLog D w u) = 0 := by
  constructor
  · intro hu
    exact (InitialThetaWittThetaPadicQuotient.mem_kernelSubmodule D w _).mp
      (periodMap_range_le_kernel D w hu)
  · exact periodLog_mem_periodRange_of_evaluation_eq_zero D w u

theorem eigenLogHom_mem_periodRange_iff (u : Principal D w) :
    eigenLogHom D w (Additive.ofMul u) ∈ (eigenPeriodMap D w).range ↔
      eigenEvaluation D w (eigenLogHom D w (Additive.ofMul u)) = 0 := by
  change eigenLogHom D w (Additive.ofMul u) ∈ (eigenPeriodMap D w).range ↔
    evaluation D w (periodLog D w u) = 0
  constructor
  · rintro ⟨v, hv⟩
    exact (periodLog_mem_periodRange_iff D w u).mp ⟨v, congrArg Subtype.val hv⟩
  · intro hu
    obtain ⟨v, hv⟩ := (periodLog_mem_periodRange_iff D w u).mpr hu
    exact ⟨v, Subtype.ext hv⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalPeriodKernel
