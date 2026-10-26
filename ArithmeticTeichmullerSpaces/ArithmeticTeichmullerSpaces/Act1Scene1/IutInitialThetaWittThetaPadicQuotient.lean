import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaPadicCompatibility
import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-PADIC-QUOTIENT
source: Joshi II `pr:teichmuller-lift-A`, the Q_p algebra evaluation
and its Tate-period kernel in the original untilt comparison.
fidelity: upgrades the existing ring quotient equivalence and its
existing quotient topology to a continuous Q_p algebra equivalence,
using the proved canonical scalar comparison. The actual theta kernel
is the closed kernel of the same continuous Q_p-linear map. It contains
the actual nonzero canonical Tate period.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no principal-ideal, full phi=p kernel,
arbitrary-untilt or period/BK comparison is assumed. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaPadicQuotient

open JoshiTeich.Prologue InitialThetaWittThetaBound InitialThetaWittThetaEvaluation
open InitialThetaWittThetaSurjective InitialThetaWittThetaQuotientTopology
open InitialThetaWittThetaPadicCompatibility
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def quotientAlgEquiv :
    (InitialThetaWittAllRadiusCompletion.Carrier D w ⧸ RingHom.ker (evaluation D w)) ≃ₐ[
      Padic (Arithmetic.residueChar w.1)] Untilt D w where
  __ := quotientEquiv D w
  commutes' a := by
    change quotientEquiv D w (Ideal.Quotient.mk (RingHom.ker (evaluation D w))
      (InitialThetaWittAllRadiusPadicScalars.commonPadicMap D w a)) = untiltPadicMap D w a
    rw [quotientEquiv_mk, evaluation_commonPadicMap]

theorem quotientAlgEquiv_apply
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w ⧸ RingHom.ker (evaluation D w)) :
    quotientAlgEquiv D w x = quotientEquiv D w x := rfl

def quotientContinuousAlgEquiv :
    (InitialThetaWittAllRadiusCompletion.Carrier D w ⧸ RingHom.ker (evaluation D w)) ≃A[
      Padic (Arithmetic.residueChar w.1)] Untilt D w where
  __ := quotientAlgEquiv D w
  continuous_toFun := quotientEquiv_continuous D w
  continuous_invFun := (quotientHomeomorph D w).symm.continuous

theorem quotientContinuousAlgEquiv_mk (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    quotientContinuousAlgEquiv D w (Ideal.Quotient.mk (RingHom.ker (evaluation D w)) x) =
      evaluation D w x := quotientEquiv_mk D w x

def kernelSubmodule : Submodule (Padic (Arithmetic.residueChar w.1))
    (InitialThetaWittAllRadiusCompletion.Carrier D w) := (evaluationContinuousLinear D w).ker

theorem mem_kernelSubmodule (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    x ∈ kernelSubmodule D w ↔ evaluation D w x = 0 := Iff.rfl

theorem kernelSubmodule_coe : (kernelSubmodule D w : Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) =
    (RingHom.ker (evaluation D w) : Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) := rfl

theorem kernelSubmodule_isClosed : IsClosed
    (kernelSubmodule D w : Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) :=
  (evaluationContinuousLinear D w).isClosed_ker

theorem tateLog_mem_kernelSubmodule (t : InitialThetaWittTateLogarithm.Tate D w) :
    InitialThetaWittTateLogarithm.tateLog D w t ∈ kernelSubmodule D w :=
  InitialThetaWittThetaTateFiber.evaluation_tateLog D w t

theorem kernelSubmodule_ne_bot : kernelSubmodule D w ≠ ⊥ := by
  intro h
  have ht := tateLog_mem_kernelSubmodule D w (InitialThetaCyclotomicTateTilt.generator D w)
  rw [h, Submodule.mem_bot] at ht
  exact InitialThetaWittTateLogarithmInjective.canonical_tateLog_ne_zero D w ht

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaPadicQuotient
