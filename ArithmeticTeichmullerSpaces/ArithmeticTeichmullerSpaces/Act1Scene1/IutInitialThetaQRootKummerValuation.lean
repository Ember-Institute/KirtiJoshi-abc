import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerValuationSplit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootKummerSeparation

/-!
source-id: JT-SCENE1-ACTUAL-QROOT-KUMMER-VALUATION
source: the actual contracting q-root, its discrete completion q-order,
and the residue-prime Kummer splitting; Joshi III 3190--3236.
fidelity: constructs a norm-one correction of the actual q-root and computes
its Kummer decomposition with prime coefficient qOrder/ramificationIndex.
The unit component remains in the original saturated unit subspace; it is
not identified with the 1+p*-qroot class or an H1e/BK class.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance valuationPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance valuationCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def qrootFieldUnit (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (localField D s)ˣ :=
  Units.mk0 ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)

theorem qroot_valuationIndex
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalCompletion.KummerValuation.valuationIndex s.1 (qrootFieldUnit D s) =
      -(Arithmetic.completionQOrder s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s) : ℤ) := by
  unfold LocalCompletion.KummerValuation.valuationIndex qrootFieldUnit
  simp only [Units.val_mk0]
  rw [Arithmetic.completionQOrder_valued s.1 _
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)
    (iutInitialThetaFullQRoot_norm_lt_one D s), WithZero.log_exp]

theorem qroot_kummer_decomposition
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootRationalKummerClass D s =
      (Arithmetic.ramIdx s.1 : ℚ_[Arithmetic.residueChar s.1])⁻¹ •
        LocalCompletion.KummerValuation.kummer s.1 (Arithmetic.residueChar s.1)
          (Ω := closure D s) (LocalCompletion.KummerValuation.correctedUnit s.1
            (Arithmetic.residueChar s.1) (qrootFieldUnit D s)) +
      ((Arithmetic.completionQOrder s.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s) : ℚ_[Arithmetic.residueChar s.1]) /
        Arithmetic.ramIdx s.1) • LocalCompletion.KummerValuation.kummer s.1
          (Arithmetic.residueChar s.1) (LocalCompletion.KummerValuation.primeUnit s.1
            (Arithmetic.residueChar s.1)) := by
  have h := LocalCompletion.KummerValuation.kummer_decomposition s.1
    (Arithmetic.residueChar s.1) (Ω := closure D s) (qrootFieldUnit D s)
  have hclass : LocalCompletion.KummerValuation.kummer s.1 (Arithmetic.residueChar s.1)
      (Ω := closure D s) (qrootFieldUnit D s) = qrootRationalKummerClass D s := rfl
  have hc : -((LocalCompletion.KummerValuation.valuationIndex s.1 (qrootFieldUnit D s) :
        ℚ_[Arithmetic.residueChar s.1]) / Arithmetic.ramIdx s.1) =
      (Arithmetic.completionQOrder s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s) : ℚ_[Arithmetic.residueChar s.1]) /
          Arithmetic.ramIdx s.1 := by
    rw [qroot_valuationIndex D s, Int.cast_neg, Int.cast_natCast, neg_div, neg_neg]
  simpa only [hclass, sub_eq_add_neg, ← neg_smul, hc] using h

theorem qroot_correction_mem_unitSubspace
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalCompletion.KummerValuation.kummer s.1 (Arithmetic.residueChar s.1)
      (Ω := closure D s) (LocalCompletion.KummerValuation.correctedUnit s.1
        (Arithmetic.residueChar s.1) (qrootFieldUnit D s)) ∈
      LocalCompletion.KummerValuation.unitsSubspace s.1 (Arithmetic.residueChar s.1) rfl :=
  LocalCompletion.KummerValuation.correctedUnit_kummer_mem s.1
    (Arithmetic.residueChar s.1) rfl (qrootFieldUnit D s)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
