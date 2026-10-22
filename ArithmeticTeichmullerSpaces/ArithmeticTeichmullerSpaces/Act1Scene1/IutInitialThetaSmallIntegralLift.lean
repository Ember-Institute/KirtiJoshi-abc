import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionSmallLogLift
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaIntegralLogCriterion

/-!
source-id: JT-SCENE1-ACTUAL-SMALL-INTEGRAL-LIFT
source: actual q-root norm and valuation, explicit small-log Kummer lift
and the original normalized rational class; Joshi III 3199--3236.
fidelity: constructs an integral lift of the original normalized class
under an explicit small q-root bound. At odd residue characteristic this
bound is equivalent to q-root order at least the local ramification index.
Sufficiently high powers of the actual q-root meet the small-log bound.
boundary: Scene1/Derived; the original j=1 bound is not presumed.
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance smallLiftPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance smallLiftCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance smallLiftAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance smallLiftContinuousSMul (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

theorem smallLift_residueChar_odd
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : Odd (Arithmetic.residueChar s.1) := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have h := B.mem_badPlaces (R.basePlace s)
  change (R.basePlace s).1 ∈ IutOddMultiplicativeSupport D at h
  rw [Arithmetic.residueChar_eq_of_liesOver (R.liesOver s)]
  exact h.1

def smallNormalizedIntegralLift
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hs : ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ≤
      ‖2 * (Arithmetic.residueChar s.1 : localField D s)‖) :
    continuousCohomology 1 (LocalKummer.padicTateTopRep (K := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1)) :=
  LocalPadicLog.smallLogIntegralLift (Ω := closure D s) (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (PaperLogWitnessHull.value D s)
      (by rwa [PaperLogWitnessHull.norm_value_eq_qroot_norm])

theorem smallNormalizedIntegralLift_standardMap
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hs : ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ≤
      ‖2 * (Arithmetic.residueChar s.1 : localField D s)‖) :
    LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) (smallNormalizedIntegralLift D s hs) =
      normalizedRationalClass D s := by
  rw [smallNormalizedIntegralLift, LocalPadicLog.smallLogIntegralLift_standardMap]
  exact congrArg Subtype.val (saturatedExp_value_eq_normalizedSaturatedClass D s)

theorem qroot_small_iff_order_ge_ramification
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ≤
        ‖2 * (Arithmetic.residueChar s.1 : localField D s)‖ ↔
      Arithmetic.ramIdx s.1 ≤ Arithmetic.completionQOrder s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s) :=
  LocalCompletion.norm_le_smallLogRadius_iff_qOrder_ge s.1 (smallLift_residueChar_odd D s) _
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s) (iutInitialThetaFullQRoot_norm_lt_one D s)

theorem normalizedClass_has_integralLift_of_order_ge_ramification
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hs : Arithmetic.ramIdx s.1 ≤ Arithmetic.completionQOrder s.1
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)) :
    ∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = normalizedRationalClass D s :=
  ⟨smallNormalizedIntegralLift D s ((qroot_small_iff_order_ge_ramification D s).mpr hs),
    smallNormalizedIntegralLift_standardMap D s _⟩

theorem eventually_qroot_power_log_mem_integralImage
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ∀ᶠ j : ℕ in Filter.atTop,
      LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ j) ∈
          LocalPadicLog.principalLogImage (Arithmetic.residueChar s.1)
            (InitialThetaLogWitness.norm_residueChar_lt_one s.1) :=
  LocalCompletion.eventually_paperNormalizedLog_mem_integralImage s.1 _
    (iutInitialThetaFullQRoot_norm_lt_one D s)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
