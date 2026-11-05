import Mathlib.Logic.Function.Conjugate
import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusInclusionSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusDenseTransport
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittFrobeniusLaws
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusNativeDiagonal
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusFrobeniusNativeFunction
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittAllRadiusComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusFrobeniusNativeFunction
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittAllRadiusComparisonNativeFunction

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-ALL-RADIUS-FROBENIUS-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on the bounded Witt period subring and its all-radius completion.
fidelity: proves that the existing actual-to-standard ring equivalence
commutes with the original forward Frobenius maps through their native function identities.
The original bounded inclusion calculation extends to the original
all-radius carriers by density and continuity. The original carriers,
ring equivalence, bounded ringFun and Frobenius maps are retained.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
boundary: Scene1/Derived; scalar and Tate-log transport, paper B/general E
identifications, and H1e/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittAllRadiusComparison

open JoshiTeich.Prologue
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeCarrierFrobeniusComparison :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
def ringEquiv_frobenius_inclusion :=
  FrobeniusInclusionSquare.commutes
    (InitialThetaPadicBoundedWittComparison.ringFun_frobenius_native D w)
    (InitialThetaWittAllRadiusCompletion.inclusion D w)
    (NativeFunction.ringEquivFun D w)
    (InitialThetaWittAllRadiusFrobenius.NativeFunction.frobeniusFun D w)
    (PadicWittAllRadiusFrobenius.NativeFunction.frobeniusFun
      (Arithmetic.residueChar w.1))
    Subtype.val
    (PadicWittAllRadiusCompletion.diagonalFun (Arithmetic.residueChar w.1))
    (PadicWittProductFrobenius.productEquiv (Arithmetic.residueChar w.1))
    Subtype.val_injective
    (InitialThetaWittAllRadiusFrobenius.NativeFunction.frobeniusFun_inclusion D w)
    (NativeFunction.ringEquivFun_inclusion_val D w)
    (PadicWittAllRadiusFrobenius.frobeniusEquiv_val (Arithmetic.residueChar w.1))
    (PadicWittProductFrobenius.productEquiv_diagonalFun (Arithmetic.residueChar w.1))

set_option linter.defProp false in
def ringEquiv_frobenius :=
  FrobeniusDenseTransport.commute_of_dense
    (InitialThetaWittAllRadiusCompletion.inclusion D w)
    (NativeFunction.ringEquivFun D w)
    (InitialThetaWittAllRadiusFrobenius.NativeFunction.frobeniusFun D w)
    (PadicWittAllRadiusFrobenius.NativeFunction.frobeniusFun
      (Arithmetic.residueChar w.1))
    (InitialThetaWittAllRadiusCompletion.inclusion_denseRange D w)
    (NativeFunction.ringEquivFun_continuous D w)
    (InitialThetaWittAllRadiusFrobenius.NativeFunction.frobeniusFun_continuous D w)
    (PadicWittAllRadiusFrobenius.frobenius_continuous (Arithmetic.residueChar w.1))
    (ringEquiv_frobenius_inclusion D w)

set_option linter.defProp false in
private def actualInverseRight :=
  (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).apply_symm_apply

set_option linter.defProp false in
private def standardInverseLeft (p : ℕ) [Fact p.Prime] :=
  (PadicWittAllRadiusFrobenius.frobeniusEquiv p).symm_apply_apply

set_option linter.defProp false in
def ringEquiv_inverseFrobenius :=
  Function.Semiconj.inverses_right (ringEquiv_frobenius D w)
    (actualInverseRight D w)
    (standardInverseLeft (Arithmetic.residueChar w.1))

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittAllRadiusComparison
