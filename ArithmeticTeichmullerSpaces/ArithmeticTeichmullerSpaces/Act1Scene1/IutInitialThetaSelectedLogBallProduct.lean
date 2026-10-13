import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperBallProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLogWitness
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogBall

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-LOG-BALL-PRODUCT
source: actual full-support q-roots, the ordinary normalized p-adic logarithm,
local log-shell surjectivity, and actual paper-corrected scalar-ball Haar volume.
fidelity: constructs full-support logarithm witnesses and identifies their
entire scalar balls with the actual q-root balls. The selected corrected
log-ball product has the paper q-sum as its negative logarithm. This does not
identify the ordinary logarithm with Bloch-Kato classes or a theta hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical Valued

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

def iutInitialThetaFullQRootLogValue
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField :=
  LocalPadicLog.normalizedLog (Arithmetic.residueChar s.1)
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)

theorem iutInitialThetaFullQRootLogValue_norm_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖iutInitialThetaFullQRootLogValue D s‖ =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ := by
  letI : CharZero (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
    charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
  exact LocalPadicLog.norm_normalizedLog (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (iutInitialThetaFullQRoot_norm_lt_one D s).le

theorem iutInitialThetaFullQRootLogValue_mem_logShell
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    iutInitialThetaFullQRootLogValue D s ∈
      LocalPadicLog.logShell (k := s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField)
        (Arithmetic.residueChar s.1) := by
  letI : CharZero (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
    charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
  exact LocalPadicLog.normalizedLog_mem_logShell (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (iutInitialThetaFullQRoot_norm_lt_one D s).le

private theorem logValue_ne_zero
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    iutInitialThetaFullQRootLogValue D s ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [iutInitialThetaFullQRootLogValue_norm_eq]
  exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)

def iutInitialThetaFullQRootLogBall
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Set (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
  (fun x => iutInitialThetaFullQRootLogValue D s * x) '' Metric.closedBall 0 1

theorem iutInitialThetaFullQRootLogBall_eq_rootBall
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    iutInitialThetaFullQRootLogBall D s = iutInitialThetaQRootIntegralBall D s := by
  unfold iutInitialThetaFullQRootLogBall iutInitialThetaQRootIntegralBall
  rw [LocalPadicLog.mul_image_closedBall _ (logValue_ne_zero D s),
    LocalPadicLog.mul_image_closedBall _
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s),
    iutInitialThetaFullQRootLogValue_norm_eq]

theorem iutInitialThetaFullQRootLogBall_subset_logShell
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    iutInitialThetaFullQRootLogBall D s ⊆
      LocalPadicLog.logShell (k := s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField)
        (Arithmetic.residueChar s.1) := by
  letI : CharZero (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
    charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
  rw [iutInitialThetaFullQRootLogBall_eq_rootBall, iutInitialThetaQRootIntegralBall,
    LocalPadicLog.mul_image_closedBall _
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)]
  exact (Metric.closedBall_subset_closedBall (iutInitialThetaFullQRoot_norm_lt_one D s).le).trans
    (LocalPadicLog.closedBall_subset_logShell (Arithmetic.residueChar_prime s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1))

theorem iutInitialThetaFullQRootLogBall_haar_toReal_eq_norm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalCompletion.normalizedHaar s.1 (iutInitialThetaFullQRootLogBall D s)).toReal =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ := by
  rw [iutInitialThetaFullQRootLogBall_eq_rootBall]
  exact iutInitialThetaQRootIntegralBall_haar_toReal_eq_norm D s

def iutInitialThetaSelectedPaperLogBallProduct
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : ℝ :=
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  ∏ s : S, (LocalCompletion.normalizedHaar s.1.1 (iutInitialThetaFullQRootLogBall D s.1)).toReal ^
    (1 / (Arithmetic.inertDeg s.1.1 : ℝ))

theorem iutInitialThetaSelectedPaperLogBallProduct_eq_rootBallProduct
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaSelectedPaperLogBallProduct D = iutInitialThetaSelectedPaperBallProduct D := by
  unfold iutInitialThetaSelectedPaperLogBallProduct iutInitialThetaSelectedPaperBallProduct
    iutInitialThetaPaperBallVolume
  simp only [iutInitialThetaFullQRootLogBall_eq_rootBall]

theorem iutInitialThetaSelectedPaperLogBallProduct_negLog_eq_paperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    -Real.log (iutInitialThetaSelectedPaperLogBallProduct D) =
      iutInitialThetaSelectedQRootPaperSum D := by
  rw [iutInitialThetaSelectedPaperLogBallProduct_eq_rootBallProduct]
  exact iutInitialThetaSelectedPaperBallProduct_negLog_eq_paperSum D

end
end JoshiTeich.Act1Scene1
