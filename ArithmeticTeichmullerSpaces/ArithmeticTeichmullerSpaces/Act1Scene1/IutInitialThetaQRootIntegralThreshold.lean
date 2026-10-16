import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSmallIntegralLift

/-!
source-id: JT-SCENE1-ACTUAL-QROOT-INTEGRAL-THRESHOLD
source: actual q-root equation, canonical base q-order accounting and
small-ball integral lifting; Joshi III 3199--3236.
fidelity: translates the small-log sufficient condition into the original
base Tate q-order. Gives the exact small-ball test for each positive power
and for a finite j-squared family in the same completion.
boundary: Scene1/Derived; the test is not asserted necessary for an integral
lift, and the power family is not identified with different untilts.
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section

namespace LocalCompletion
open NumberField

theorem norm_le_smallLogRadius_iff_ordp_ge_one
    {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
    (hp : Odd (Arithmetic.residueChar w)) (y : completionAt K w)
    (hy0 : y ≠ 0) (hy1 : ‖y‖ < 1) :
    ‖y‖ ≤ ‖2 * (Arithmetic.residueChar w : completionAt K w)‖ ↔
      1 ≤ Arithmetic.ordp w y := by
  have ho : Arithmetic.ordp w y =
      (Arithmetic.completionQOrder w y : ℝ) / Arithmetic.ramIdx w := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_neg] using
      Arithmetic.ordp_eq_of_valued w y _ (Arithmetic.completionQOrder_valued w y hy0 hy1)
  rw [norm_le_smallLogRadius_iff_qOrder_ge w hp y hy0 hy1, ho,
    le_div_iff₀ (by exact_mod_cast Arithmetic.ramIdx_pos w), one_mul, Nat.cast_le]

end LocalCompletion

namespace PrincipalUnitKummer
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance thresholdPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance thresholdCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def baseIntegralThreshold
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : ℕ :=
  2 * D.prime.ℓ * Arithmetic.ramIdx
    ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1

theorem baseIntegralThreshold_pos
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    0 < baseIntegralThreshold D s := by
  have hl : 0 < D.prime.ℓ := lt_of_lt_of_le (by decide : 0 < 5) D.prime.five_le
  exact Nat.mul_pos (Nat.mul_pos (by decide) hl) (Arithmetic.ramIdx_pos _)

theorem qroot_ordp_eq_baseQOrder
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Arithmetic.ordp s.1 ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s) =
      ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s) : ℝ) /
        baseIntegralThreshold D s := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  have hTate : ∀ w : B.badFinset,
      Valued.v (B.tateParameter w) = WithZero.exp (-(B.qOrder w : ℤ)) := by
    intro w
    exact iutCompletionQOrder_valued w.1 _
      (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w)
  have hl : 0 < D.prime.ℓ := lt_of_lt_of_le (by decide : 0 < 5) D.prime.five_le
  have ho := IutTorsionQRootSource.canonical_qroot_ordp_eq B R.qroot R.qroot_pow_eq hTate hl s
  have hb : R.basePlace s = IutTorsionQRootSource.basePlaceOf (B := B) s := by
    apply Subtype.ext
    exact (iutPlaceUnder_eq_of_liesOver (R.liesOver s)).trans
      (iutPlaceUnder_eq_of_liesOver (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) s)).symm
  simpa [B, R, baseIntegralThreshold, hb] using ho

theorem qroot_power_small_iff_baseQOrder
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (n : ℕ) (hn : 0 < n) :
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ n‖ ≤
        ‖2 * (Arithmetic.residueChar s.1 : localField D s)‖ ↔
      baseIntegralThreshold D s ≤ n * (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s) := by
  rw [LocalCompletion.norm_le_smallLogRadius_iff_ordp_ge_one s.1
    (smallLift_residueChar_odd D s) _
    (pow_ne_zero _ ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s))
    (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (iutInitialThetaFullQRoot_norm_lt_one D s) hn.ne'),
    Arithmetic.ordp_pow, qroot_ordp_eq_baseQOrder, ← mul_div_assoc,
    le_div_iff₀ (by exact_mod_cast baseIntegralThreshold_pos D s), one_mul, ← Nat.cast_mul, Nat.cast_le]

theorem qroot_small_iff_baseQOrder
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ ≤
        ‖2 * (Arithmetic.residueChar s.1 : localField D s)‖ ↔
      baseIntegralThreshold D s ≤ (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s) := by
  simpa only [pow_one, one_mul] using qroot_power_small_iff_baseQOrder D s 1 (by decide)

theorem normalizedClass_has_integralLift_of_baseQOrder
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hs : baseIntegralThreshold D s ≤ (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s)) :
    ∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x = normalizedRationalClass D s :=
  ⟨smallNormalizedIntegralLift D s ((qroot_small_iff_baseQOrder D s).mpr hs),
    smallNormalizedIntegralLift_standardMap D s _⟩

theorem finite_qroot_square_small_iff_baseQOrder
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (m : ℕ) (hm : 1 ≤ m) :
    (∀ j ∈ Finset.Icc 1 m,
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ (j ^ 2)‖ ≤
        ‖2 * (Arithmetic.residueChar s.1 : localField D s)‖) ↔
      baseIntegralThreshold D s ≤ (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s) := by
  constructor
  · intro h
    apply (qroot_small_iff_baseQOrder D s).mp
    have h1 := h 1 (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩)
    simpa only [one_pow, pow_one] using h1
  · intro hs j hj
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    apply (qroot_power_small_iff_baseQOrder D s (j ^ 2) (pow_pos hjpos _)).mpr
    exact hs.trans (by
      calc
        _ = 1 * (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
            ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s) := by rw [one_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ (pow_pos hjpos 2))

end PrincipalUnitKummer
end
end JoshiTeich.Act1Scene1
