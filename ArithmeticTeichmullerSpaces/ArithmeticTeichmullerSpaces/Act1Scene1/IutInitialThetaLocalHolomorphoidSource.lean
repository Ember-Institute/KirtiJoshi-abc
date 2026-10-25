import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltSharp
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalGeometricFontaine

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-INITIAL-THETA-LOCAL-HOLOMORPHOID-SOURCE
source: the actual coefficient completion, tilt carrier, sharp map and
Fontaine theta map from `IutInitialThetaCanonicalGeometricFontaine.lean`,
`IutInitialThetaTiltField.lean`, and `IutInitialThetaTiltSharp.lean`.
fidelity: packages only the local source laws already proved for the same
InitialThetaData supported place. The global holomorphoid, cross-place marking,
tempered marking, and paper holomorphoid identity remain separate.
boundary: Scene1/Derived; local actual source package only.
-/

namespace InitialThetaLocalHolomorphoidSource

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

local instance selectedPrimeNorm :
    Fact (0 < ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

abbrev Untilt := InitialThetaCanonicalGeometricFontaine.coefficientField D w
abbrev Tilt := InitialThetaTiltField.Carrier D w

def sharp : Tilt D w →*₀ Untilt D w :=
  InitialThetaTiltSharp.sharp D w

def theta :
    WittVector (Arithmetic.residueChar w.1)
        (InitialThetaTiltField.Source D w) →
      LocalGeometricFontaine.integerRing (Untilt D w) :=
  (InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta

structure Data (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaTateParameterData D).places) : Type (u + 1) where
  sharp_surjective : Function.Surjective (sharp D w)
  sharp_norm : ∀ x : Tilt D w, ‖sharp D w x‖₊ = InitialThetaTiltField.valuation D w x
  theta_surjective : Function.Surjective (theta D w)
  theta_teichmuller : ∀ x : InitialThetaTiltField.Source D w,
    ((theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) x) :
      LocalGeometricFontaine.integerRing (Untilt D w)) : Untilt D w) =
      sharp D w (InitialThetaTiltField.inclusion D w x)

noncomputable def canonical : Data D w where
  sharp_surjective := InitialThetaTiltSharp.sharp_surjective D w
  sharp_norm := InitialThetaTiltSharp.sharp_norm D w
  theta_surjective := InitialThetaCanonicalGeometricFontaine.theta_surjective D w
  theta_teichmuller := InitialThetaTiltSharp.theta_teichmuller_eq_sharp D w

theorem canonical_sharp_norm (x : Tilt D w) :
    ‖sharp D w x‖₊ = InitialThetaTiltField.valuation D w x :=
  (canonical D w).sharp_norm x

theorem canonical_theta_teichmuller (x : InitialThetaTiltField.Source D w) :
    ((theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) x) :
      LocalGeometricFontaine.integerRing (Untilt D w)) : Untilt D w) =
      sharp D w (InitialThetaTiltField.inclusion D w x) :=
  (canonical D w).theta_teichmuller x

end InitialThetaLocalHolomorphoidSource

end
end JoshiTeich.Act1Scene1
