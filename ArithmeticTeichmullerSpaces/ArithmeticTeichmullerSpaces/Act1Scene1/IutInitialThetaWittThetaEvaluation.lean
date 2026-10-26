import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaBound
import Mathlib.Topology.Algebra.UniformRing

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-EVALUATION
source: Joshi II `pr:teichmuller-lift-A`, the continuous canonical
evaluation from the period ring to its original untilt.
fidelity: extends the original bounded Witt evaluation to its proved
contractive radius completion, then composes with the original common
ring coordinate. Proves continuity, contraction and agreement with the
original Fontaine map. No extension or continuity is an input.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; arbitrary untilts and paper period/BK
comparisons remain open. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaEvaluation

open JoshiTeich.Prologue InitialThetaWittThetaBound
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def sourceHom : InitialThetaWittRhoCompletion.Source D w (radius D w) →+* Untilt D w :=
  (InitialThetaBoundedWittLocalization.evaluation D w).comp
    (InitialThetaWittRhoCompletion.sourceEquiv D w (radius D w)).symm.toRingHom

theorem sourceHom_lipschitz : LipschitzWith 1 (sourceHom D w) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
  exact evaluation_norm_le D w ((InitialThetaWittRhoCompletion.sourceEquiv D w (radius D w)).symm (x - y))

theorem sourceHom_continuous : Continuous (sourceHom D w) := (sourceHom_lipschitz D w).continuous

def completedHom : InitialThetaWittRhoCompletion.Completed D w (radius D w) →+* Untilt D w :=
  UniformSpace.Completion.extensionHom (sourceHom D w) (sourceHom_continuous D w)

theorem completedHom_continuous : Continuous (completedHom D w) :=
  UniformSpace.Completion.continuous_extension

theorem completedHom_inclusion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    completedHom D w (InitialThetaWittRhoCompletion.inclusion D w (radius D w) x) =
      InitialThetaBoundedWittLocalization.evaluation D w x :=
  UniformSpace.Completion.extensionHom_coe (sourceHom D w) (sourceHom_continuous D w)
    (InitialThetaWittRhoCompletion.sourceEquiv D w (radius D w) x)

theorem completedHom_norm_le (x : InitialThetaWittRhoCompletion.Completed D w (radius D w)) :
    ‖completedHom D w x‖ ≤ ‖x‖ := by
  refine (InitialThetaWittRhoCompletion.inclusion_denseRange D w (radius D w)).induction_on x
    (isClosed_le (completedHom_continuous D w).norm continuous_norm) ?_
  intro a
  rw [completedHom_inclusion, InitialThetaWittRhoCompletion.inclusion_norm]
  exact evaluation_norm_le D w a

def evaluation : InitialThetaWittAllRadiusCompletion.Carrier D w →+* Untilt D w :=
  (completedHom D w).comp (InitialThetaWittAllRadiusCompletion.evaluate D w (radius D w))

theorem evaluation_continuous : Continuous (evaluation D w) :=
  (completedHom_continuous D w).comp (InitialThetaWittAllRadiusCompletion.evaluate_continuous D w (radius D w))

theorem evaluation_inclusion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    evaluation D w (InitialThetaWittAllRadiusCompletion.inclusion D w x) =
      InitialThetaBoundedWittLocalization.evaluation D w x := completedHom_inclusion D w x

theorem evaluation_ainfMap (a : Ainf D w) :
    evaluation D w (InitialThetaWittAllRadiusExpansion.ainfMap D w a) = integralEvaluation D w a := by
  rw [InitialThetaWittAllRadiusExpansion.ainfMap, RingHom.comp_apply, evaluation_inclusion]
  exact InitialThetaBoundedWittLocalization.evaluation_inclusion D w a

theorem evaluation_norm_le (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    ‖evaluation D w x‖ ≤ InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w (radius D w) x :=
  completedHom_norm_le D w _

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaEvaluation
