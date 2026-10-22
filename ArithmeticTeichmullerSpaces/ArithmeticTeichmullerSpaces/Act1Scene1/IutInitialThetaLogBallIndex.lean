import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLogBallHaar
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarIndex

/-!
source-id: JT-SCENE1-INITIAL-THETA-LOG-BALL-INDEX
fidelity: computes the actual q-root logarithm integral-ball Haar measure
by the finite additive index of its principal ideal. The residue-field
cardinality and completion-norm identification remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaLogWitness

open JoshiTeich.Prologue NumberField MeasureTheory

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-- The actual logarithm witness, bundled in the completion's integer ring. -/
def integralValue (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    LocalCompletion.integerRing v.1 :=
  ⟨value D v, Valued.toNormedField.norm_le_one_iff.mp (by
    rw [norm_value_eq_qroot_norm D v]
    exact (IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v).le)⟩

theorem integralValue_ne_zero
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    integralValue D v ≠ 0 := by
  intro h
  exact value_ne_zero D v (congrArg (fun x : LocalCompletion.integerRing v.1 =>
    (x : v.1.maximalIdeal.adicCompletion ↥D.prime.torsionField)) h)

theorem integralBall_index_pos
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    0 < LocalCompletion.principalIndex v.1 (integralValue D v) :=
  LocalCompletion.principalIndex_pos v.1 _ (integralValue_ne_zero D v)

theorem integralBall_haar_eq_inv_index
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    LocalCompletion.normalizedHaar v.1 (integralBall D v) =
      (LocalCompletion.principalIndex v.1 (integralValue D v) : ENNReal)⁻¹ := by
  simpa only [integralBall, integralValue] using
    (LocalCompletion.normalizedHaar_scalarBall_eq_inv_index v.1
      (integralValue D v) (integralValue_ne_zero D v))

theorem integralBall_haar_le_one
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    LocalCompletion.normalizedHaar v.1 (integralBall D v) ≤ 1 := by
  apply (measure_mono ?_).trans_eq (LocalCompletion.normalizedHaar_unitBall v.1)
  rw [integralBall_eq_closedBall D v]
  exact Metric.closedBall_subset_closedBall
    (IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one D v).le

end
end JoshiTeich.Act1Scene1.InitialThetaLogWitness
