import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittRationalScalars
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ALL-RADIUS-RATIONAL-SCALARS
source: Joshi II `se:ff-rings`, rational scalars in the completed period
ring and the scalar-preserving Frobenius action.
fidelity: transports one actual rational embedding through the original
localization inclusions to every fixed-radius completion and the common
complete ring. The coordinate maps preserve these scalars, and the
actual all-radius Frobenius becomes a rational algebra automorphism.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no continuity for the usual real topology on
the rationals is claimed. P-adic scalars, multiplicative norm equality,
Tate-log eigenspace and paper B/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusRationalScalars

open JoshiTeich.Prologue
open InitialThetaBoundedWittRationalScalars
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

def completedRationalMap (ρ : Radius) : ℚ →+* InitialThetaWittRhoCompletion.Completed D w ρ :=
  (InitialThetaWittRhoCompletion.inclusion D w ρ).comp (rationalMap D w)

instance completedRatAlgebra (ρ : Radius) :
    Algebra ℚ (InitialThetaWittRhoCompletion.Completed D w ρ) :=
  (completedRationalMap D w ρ).toAlgebra

def commonRationalMap : ℚ →+* Carrier D w :=
  (InitialThetaWittAllRadiusCompletion.inclusion D w).comp (rationalMap D w)

instance commonRatAlgebra : Algebra ℚ (Carrier D w) := (commonRationalMap D w).toAlgebra

theorem commonRationalMap_injective : Function.Injective (commonRationalMap D w) :=
  (InitialThetaWittAllRadiusCompletion.inclusion_injective D w).comp (rationalMap_injective D w)

theorem evaluate_rational (ρ : Radius) (q : ℚ) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (commonRationalMap D w q) =
      completedRationalMap D w ρ q := rfl

theorem inclusion_smul (q : ℚ) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittAllRadiusCompletion.inclusion D w (q • x) =
      q • InitialThetaWittAllRadiusCompletion.inclusion D w x := by
  simp only [Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap]

theorem evaluate_smul (ρ : Radius) (q : ℚ) (x : Carrier D w) :
    InitialThetaWittAllRadiusCompletion.evaluate D w ρ (q • x) =
      q • InitialThetaWittAllRadiusCompletion.evaluate D w ρ x := by
  simp only [Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap]

theorem frobenius_rational (q : ℚ) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (commonRationalMap D w q) =
      commonRationalMap D w q :=
  RingHom.map_rat_algebraMap (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).toRingHom q

def frobeniusAlgEquiv : Carrier D w ≃ₐ[ℚ] Carrier D w where
  __ := InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
  commutes' := frobenius_rational D w

theorem frobenius_smul (q : ℚ) (x : Carrier D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (q • x) =
      q • InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x :=
  map_smul (frobeniusAlgEquiv D w) q x

theorem frobeniusAlgEquiv_continuous : Continuous (frobeniusAlgEquiv D w) :=
  InitialThetaWittAllRadiusFrobenius.frobenius_continuous D w

end
end JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusRationalScalars
