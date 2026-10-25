import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittPadicScalars
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusRationalScalars

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ALL-RADIUS-PADIC-SCALARS
source: Joshi II `se:ff-rings`, the Q_p algebra of completed period
elements and its scalar-preserving Frobenius.
fidelity: transports the same actual Q_p embedding to every radius
completion and the common complete ring, retaining rational compatibility.
The inclusion and coordinate maps preserve scalars, and the all-radius
Frobenius is a Q_p algebra automorphism.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; continuity of the scalar embedding/action,
scalar norm laws, Tate-log and paper B/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusPadicScalars

open JoshiTeich.Prologue
open InitialThetaBoundedWittPadicScalars
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

def completedPadicMap (ρ : Radius) :
    Padic (Arithmetic.residueChar w.1) →+* InitialThetaWittRhoCompletion.Completed D w ρ :=
  (InitialThetaWittRhoCompletion.inclusion D w ρ).comp (padicMap D w)

instance completedPadicAlgebra (ρ : Radius) :
    Algebra (Padic (Arithmetic.residueChar w.1)) (InitialThetaWittRhoCompletion.Completed D w ρ) :=
  (completedPadicMap D w ρ).toAlgebra

def commonPadicMap : Padic (Arithmetic.residueChar w.1) →+* Carrier D w :=
  (InitialThetaWittAllRadiusCompletion.inclusion D w).comp (padicMap D w)

instance commonPadicAlgebra : Algebra (Padic (Arithmetic.residueChar w.1)) (Carrier D w) :=
  (commonPadicMap D w).toAlgebra

theorem commonPadicMap_injective : Function.Injective (commonPadicMap D w) :=
  (InitialThetaWittAllRadiusCompletion.inclusion_injective D w).comp (padicMap_injective D w)

theorem evaluate_padic (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1)) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (commonPadicMap D w a) =
      completedPadicMap D w ρ a := rfl

theorem commonPadicMap_rational (q : ℚ) :
    commonPadicMap D w (algebraMap ℚ (Padic (Arithmetic.residueChar w.1)) q) =
      InitialThetaWittAllRadiusRationalScalars.commonRationalMap D w q :=
  congrArg (InitialThetaWittAllRadiusCompletion.inclusion D w) (padicMap_rational D w q)

theorem inclusion_smul (a : Padic (Arithmetic.residueChar w.1))
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittAllRadiusCompletion.inclusion D w (a • x) =
      a • InitialThetaWittAllRadiusCompletion.inclusion D w x :=
  map_mul (InitialThetaWittAllRadiusCompletion.inclusion D w) (padicMap D w a) x

theorem evaluate_smul (ρ : Radius) (a : Padic (Arithmetic.residueChar w.1)) (x : Carrier D w) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (a • x) =
      a • InitialThetaWittAllRadiusCompletion.evaluate D w ρ x :=
  map_mul (InitialThetaWittAllRadiusCompletion.evaluate D w ρ) (commonPadicMap D w a) x

def evaluateAlgHom (ρ : Radius) :
    Carrier D w →ₐ[Padic (Arithmetic.residueChar w.1)] InitialThetaWittRhoCompletion.Completed D w ρ where
  __ := InitialThetaWittAllRadiusCompletion.evaluate D w ρ
  commutes' := evaluate_padic D w ρ

theorem frobenius_padic (a : Padic (Arithmetic.residueChar w.1)) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (commonPadicMap D w a) =
      commonPadicMap D w a := by
  change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
    (InitialThetaWittAllRadiusCompletion.inclusion D w (padicMap D w a)) = _
  rw [InitialThetaWittAllRadiusFrobenius.frobenius_inclusion,
    InitialThetaBoundedWittPadicScalars.frobenius_padic]
  rfl

def frobeniusAlgEquiv : Carrier D w ≃ₐ[Padic (Arithmetic.residueChar w.1)] Carrier D w where
  __ := InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
  commutes' := frobenius_padic D w

theorem frobenius_smul (a : Padic (Arithmetic.residueChar w.1)) (x : Carrier D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (a • x) =
      a • InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x :=
  map_smul (frobeniusAlgEquiv D w) a x

theorem frobeniusAlgEquiv_continuous : Continuous (frobeniusAlgEquiv D w) :=
  InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w

end
end JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusPadicScalars
