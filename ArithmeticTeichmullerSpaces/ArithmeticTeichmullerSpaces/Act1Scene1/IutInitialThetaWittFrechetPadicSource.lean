import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPadicScalarContinuity
import Mathlib.Topology.Algebra.UniformMulAction

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PADIC-SOURCE
source: Joshi II `se:ff-rings`, the Q_p algebra of bounded period
elements before completion for the family of rho norms.
fidelity: puts the original bounded Witt Q_p embedding on the actual
all-radius source copy. Its continuity follows from the original common
embedding and the proved uniform-inducing inclusion. The resulting
scalar action is jointly continuous and each constant scalar action
uniformly continuous, as required by the standard completion algebra.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; completion algebra comparison and full paper
period/BK identities remain separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPadicSource

open JoshiTeich.Prologue InitialThetaWittFrechetSource
open InitialThetaWittAllRadiusPadicScalars
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def sourcePadicMap : Padic (Arithmetic.residueChar w.1) →+* Source D w :=
  (sourceEquiv D w).toRingHom.comp (InitialThetaBoundedWittPadicScalars.padicMap D w)

instance sourcePadicAlgebra : Algebra (Padic (Arithmetic.residueChar w.1)) (Source D w) :=
  (sourcePadicMap D w).toAlgebra

theorem sourcePadicMap_injective : Function.Injective (sourcePadicMap D w) :=
  (sourceEquiv D w).injective.comp (InitialThetaBoundedWittPadicScalars.padicMap_injective D w)

theorem toCarrier_padic (a : Padic (Arithmetic.residueChar w.1)) :
    toCarrier D w (sourcePadicMap D w a) = commonPadicMap D w a := rfl

theorem sourcePadicMap_continuous : Continuous (sourcePadicMap D w) := by
  apply (toCarrier_isUniformInducing D w).isInducing.continuous_iff.mpr
  simpa only [Function.comp_def, toCarrier_padic] using
    InitialThetaWittPadicScalarContinuity.commonPadicMap_continuous D w

instance sourceContinuousSMul : ContinuousSMul (Padic (Arithmetic.residueChar w.1)) (Source D w) :=
  continuousSMul_of_algebraMap _ _ (sourcePadicMap_continuous D w)

instance sourceUniformContinuousConstSMul :
    UniformContinuousConstSMul (Padic (Arithmetic.residueChar w.1)) (Source D w) :=
  uniformContinuousConstSMul_of_continuousConstSMul (Padic (Arithmetic.residueChar w.1)) (Source D w)

def toCarrierAlgHom : Source D w →ₐ[Padic (Arithmetic.residueChar w.1)] Carrier D w where
  __ := toCarrier D w
  commutes' := toCarrier_padic D w

def sourceAlgEquiv : InitialThetaBoundedWittLocalization.Ring D w ≃ₐ[
    Padic (Arithmetic.residueChar w.1)] Source D w where
  __ := sourceEquiv D w
  commutes' _a := rfl

theorem toCarrier_smul (a : Padic (Arithmetic.residueChar w.1)) (x : Source D w) :
    toCarrier D w (a • x) = a • toCarrier D w x := map_smul (toCarrierAlgHom D w) a x

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPadicSource
