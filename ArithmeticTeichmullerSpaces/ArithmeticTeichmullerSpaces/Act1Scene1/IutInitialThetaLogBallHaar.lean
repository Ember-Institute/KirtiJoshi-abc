import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLogBall
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaar

/-!
source-id: JT-SCENE1-INITIAL-THETA-LOG-BALL-HAAR
source: Joshi III, normalized local Haar measure and `le:volume-lemma1`;
the actual InitialThetaData logarithm integral ball.
fidelity: supplies actual positive finite Haar measure and the scalar
Haar-character formula. It does not identify that character with the
paper norm or construct the tensor hull and its global volume.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaLogWitness

open JoshiTeich.Prologue NumberField MeasureTheory

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem integralBall_isCompact
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    IsCompact (integralBall D v) := by
  rw [integralBall_eq_closedBall D v]
  exact isCompact_closedBall _ _

theorem integralBall_isOpen
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    IsOpen (integralBall D v) := by
  rw [integralBall_eq_closedBall D v]
  exact IsUltrametricDist.isOpen_closedBall _
    (norm_ne_zero_iff.mpr ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot_ne_zero v))

theorem integralBall_haar_eq
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    LocalCompletion.normalizedHaar v.1 (integralBall D v) =
      (distribHaarChar (v.1.maximalIdeal.adicCompletion ↥D.prime.torsionField)
        (Units.mk0 (value D v) (value_ne_zero D v)) : ENNReal) := by
  exact LocalCompletion.normalizedHaar_scalarBall v.1 _ (value_ne_zero D v)

theorem integralBall_haar_pos_lt_top
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    0 < LocalCompletion.normalizedHaar v.1 (integralBall D v) ∧
      LocalCompletion.normalizedHaar v.1 (integralBall D v) < ⊤ := by
  rw [integralBall_haar_eq D v]
  exact ⟨ENNReal.coe_pos.mpr (distribHaarChar_pos), ENNReal.coe_lt_top⟩

end
end JoshiTeich.Act1Scene1.InitialThetaLogWitness
