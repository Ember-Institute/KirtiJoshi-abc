import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalTatePrincipalLift

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-EVALUATION-SURJECTIVE
source: Joshi II `eq:tate-module-of-lubin-tate` and the period sequence
in the proof of `pr:teichmuller-lift-A`, with the multiplicative formal group.
fidelity: the actual small-ball logarithm inverse produces principal tilt
units, not just arbitrary phi=p elements. Actual inverse Frobenius roots
remove the p-power scaling and prove logarithmic evaluation is surjective
from the original principal-unit group onto the original untilt. The actual
rational Tate lift is injective and its range is exactly this evaluation
kernel, giving exactness on the original multiplicative-formal-group source.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the full phi=p carrier is retained. Identifying
every phi=p element with a principal logarithm remains open. No exactness,
scalar action on principal units or representation law is input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalEvaluationSurjective

open JoshiTeich.Prologue InitialThetaWittThetaBound InitialThetaWittThetaEvaluation
open InitialThetaWittThetaPadicCompatibility InitialThetaWittPrincipalUnitDomain
open InitialThetaWittPrincipalUnitPeriod InitialThetaWittPrincipalUnitLift
open InitialThetaWittPrincipalPrimeDivision InitialThetaWittRationalTatePrincipalLift
open InitialThetaWittLogarithmSeries InitialThetaWittEigenEvaluationSurjective
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

theorem exists_local_principal_preimage : ∃ R : ℝ, 0 < R ∧
    ∀ y : Untilt D w, ‖y‖ ≤ R → ∃ u : Principal D w, evaluation D w (periodLog D w u) = y := by
  obtain ⟨k, hk⟩ := exists_coefficient_bound D w
  obtain ⟨R, hR, hR1, hlocal⟩ :=
    UltrametricPowerSeriesLocalSurjectivity.exists_local_surjectivity
      (untiltLogCoefficient D w) k hk (untiltLogCoefficient_zero D w) (untiltLogCoefficient_one D w)
  refine ⟨R, hR, fun y hy => ?_⟩
  obtain ⟨a, ha, hsum⟩ := hlocal y hy
  have hnear : ‖(1 + a) - 1‖ < 1 := by
    simpa only [add_sub_cancel_left] using ha.trans_lt hR1
  have hn : ‖1 + a‖ = 1 := UltrametricPrincipalUnits.norm_eq_one _ hnear
  have ha0 : 1 + a ≠ 0 := norm_pos_iff.mp (hn ▸ zero_lt_one)
  let z : UntilPrincipal D w := ⟨Units.mk0 (1 + a) ha0, hnear⟩
  refine ⟨principalLift D w z, ?_⟩
  have ht := hasSum_evaluation_periodLog D w (principalLift D w z)
  rw [untiltCoordinate_principalLift] at ht
  have ht' : HasSum (fun n : ℕ => logCoefficient D w n • a ^ n)
      (evaluation D w (periodLog D w (principalLift D w z))) := by
    simpa only [z, Units.val_mk0, add_sub_cancel_left] using ht
  exact ht'.unique (by simpa only [untiltLogCoefficient_mul] using hsum)

def principalEvaluationHom : Additive (Principal D w) →+ Untilt D w :=
  (evaluation D w).toAddMonoidHom.comp (periodLogHom D w)

theorem principalEvaluationHom_surjective : Function.Surjective (principalEvaluationHom D w) := by
  obtain ⟨R, hR, hlocal⟩ := exists_local_principal_preimage D w
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hR hy0)
    (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2
  let a : Padic (Arithmetic.residueChar w.1) :=
    (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k
  have ha : a ≠ 0 := pow_ne_zero k
    (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  have hsmall : ‖a • y‖ ≤ R := by
    change ‖untiltPadicMap D w a * y‖ ≤ R
    dsimp only [a]
    rw [map_pow, map_natCast, norm_mul, norm_pow]
    exact ((lt_div_iff₀ hy0).mp hk).le
  obtain ⟨u, hu⟩ := hlocal (a • y) hsmall
  refine ⟨Additive.ofMul (primeRoot D w k u), ?_⟩
  change evaluation D w (periodLog D w (Additive.ofMul (primeRoot D w k u)).toMul) = y
  rw [toMul_ofMul, periodLog_primeRoot, evaluation_smul, hu, inv_smul_smul₀ ha]

theorem rationalPrincipalHom_range :
    (rationalPrincipalHom D w).range = (principalEvaluationHom D w).ker := by
  ext u
  change (∃ v, rationalPrincipalHom D w v = u) ↔ evaluation D w (periodLog D w u.toMul) = 0
  constructor
  · rintro ⟨v, rfl⟩
    change evaluation D w (periodLogHom D w (rationalPrincipalHom D w v)) = 0
    rw [periodLogHom_rationalPrincipalHom]
    exact (InitialThetaWittThetaPadicQuotient.mem_kernelSubmodule D w _).mp
      (periodMap_range_le_kernel D w ⟨v, rfl⟩)
  · intro hu
    obtain ⟨v, hv⟩ := periodLog_mem_periodRange_of_evaluation_eq_zero D w u.toMul hu
    refine ⟨v, InitialThetaWittPrincipalUnitInjective.periodLogHom_injective D w ?_⟩
    rw [periodLogHom_rationalPrincipalHom]
    exact hv

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalEvaluationSurjective
