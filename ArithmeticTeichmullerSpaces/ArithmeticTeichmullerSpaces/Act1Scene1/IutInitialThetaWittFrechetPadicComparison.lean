import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetPadicSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPadicScalarNorm
import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FRECHET-PADIC-COMPARISON
source: Joshi II `se:ff-rings`, the topological Q_p algebra structure
on the all-radius completion underlying `pr:teichmuller-lift-A/B`.
fidelity: uses the standard completion algebra of the original bounded
Witt Q_p action. Proves that the canonical completion comparison preserves
the same original p-adic embedding, and bundles it as a continuous algebra
equivalence. The original inclusion and radius maps are algebra maps;
the original exact radius scalar-norm law holds on this completion.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; normalized Q_p seminorms and full paper
period/BK comparisons remain separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrechetPadicComparison

open JoshiTeich.Prologue InitialThetaWittFrechetSource
open InitialThetaWittFrechetComparison InitialThetaWittFrechetPadicSource
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

instance completedPadicAlgebra : Algebra (Padic (Arithmetic.residueChar w.1)) (Completed D w) :=
  UniformSpace.Completion.algebra (Source D w) (Padic (Arithmetic.residueChar w.1))

def completedPadicMap : Padic (Arithmetic.residueChar w.1) →+* Completed D w :=
  algebraMap _ _

theorem completedPadicMap_coe (a : Padic (Arithmetic.residueChar w.1)) :
    completedPadicMap D w a = (sourcePadicMap D w a : Completed D w) := rfl

theorem completedPadicMap_continuous : Continuous (completedPadicMap D w) := by
  change Continuous (fun a => (sourcePadicMap D w a : Completed D w))
  exact (UniformSpace.Completion.continuous_coe (Source D w)).comp (sourcePadicMap_continuous D w)

instance completedContinuousSMul : ContinuousSMul (Padic (Arithmetic.residueChar w.1)) (Completed D w) :=
  continuousSMul_of_algebraMap _ _ (completedPadicMap_continuous D w)

theorem ringEquiv_padic (a : Padic (Arithmetic.residueChar w.1)) :
    ringEquiv D w (completedPadicMap D w a) = InitialThetaWittAllRadiusPadicScalars.commonPadicMap D w a := by
  rw [completedPadicMap_coe, ringEquiv_coe, toCarrier_padic]

theorem completedPadicMap_injective : Function.Injective (completedPadicMap D w) := by
  intro a b h
  apply InitialThetaWittAllRadiusPadicScalars.commonPadicMap_injective D w
  simpa only [ringEquiv_padic] using congrArg (ringEquiv D w) h

def algEquiv : Completed D w ≃ₐ[Padic (Arithmetic.residueChar w.1)] Carrier D w where
  __ := ringEquiv D w
  commutes' := ringEquiv_padic D w

def continuousAlgEquiv : Completed D w ≃A[Padic (Arithmetic.residueChar w.1)] Carrier D w where
  __ := algEquiv D w
  continuous_toFun := ringEquiv_continuous D w
  continuous_invFun := ringEquiv_symm_continuous D w

theorem algEquiv_smul (a : Padic (Arithmetic.residueChar w.1)) (x : Completed D w) :
    ringEquiv D w (a • x) = a • ringEquiv D w x := map_smul (algEquiv D w) a x

def coeAlgHom : Source D w →ₐ[Padic (Arithmetic.residueChar w.1)] Completed D w where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _a := rfl

def originalInclusionAlgHom : InitialThetaBoundedWittLocalization.Ring D w →ₐ[
    Padic (Arithmetic.residueChar w.1)] Completed D w :=
  (coeAlgHom D w).comp (sourceAlgEquiv D w).toAlgHom

theorem originalInclusionAlgHom_apply (x : InitialThetaBoundedWittLocalization.Ring D w) :
    originalInclusionAlgHom D w x = originalInclusion D w x := rfl

def radiusAlgHom (ρ : InitialThetaWittRhoCompletion.Radius) :
    Completed D w →ₐ[Padic (Arithmetic.residueChar w.1)] InitialThetaWittRhoCompletion.Completed D w ρ :=
  (InitialThetaWittAllRadiusPadicScalars.evaluateAlgHom D w ρ).comp (algEquiv D w).toAlgHom

theorem radiusAlgHom_apply (ρ : InitialThetaWittRhoCompletion.Radius) (x : Completed D w) :
    radiusAlgHom D w ρ x = radiusMap D w ρ x := rfl

theorem radiusMap_padic (ρ : InitialThetaWittRhoCompletion.Radius)
    (a : Padic (Arithmetic.residueChar w.1)) :
    radiusMap D w ρ (completedPadicMap D w a) =
      InitialThetaWittAllRadiusPadicScalars.completedPadicMap D w ρ a :=
  (radiusAlgHom D w ρ).commutes a

theorem radiusMap_smul (ρ : InitialThetaWittRhoCompletion.Radius)
    (a : Padic (Arithmetic.residueChar w.1)) (x : Completed D w) :
    radiusMap D w ρ (a • x) = a • radiusMap D w ρ x := map_smul (radiusAlgHom D w ρ) a x

theorem norm_radiusMap_smul (ρ : InitialThetaWittRhoCompletion.Radius)
    (a : Padic (Arithmetic.residueChar w.1)) (x : Completed D w) :
    ‖radiusMap D w ρ (a • x)‖ =
      ‖InitialThetaWittAllRadiusPadicScalars.completedPadicMap D w ρ a‖ * ‖radiusMap D w ρ x‖ := by
  rw [radiusMap_smul, InitialThetaWittPadicScalarNorm.norm_padic_smul]

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrechetPadicComparison
