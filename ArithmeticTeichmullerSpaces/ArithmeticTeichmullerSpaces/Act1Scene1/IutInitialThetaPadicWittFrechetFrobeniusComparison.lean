import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittAllRadiusFrobeniusComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusCompletionSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrechetComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrechetFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FRECHET-FROBENIUS-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on the bounded Witt period subring and its all-radius completion.
fidelity: proves that the existing actual-to-standard comparison commutes
with Frobenius on the original Hausdorff completions and with inverse
Frobenius. A generic function square consumes the proved native all-radius
naturality and separately cached original completion-to-carrier laws.
The original carriers,
ring equivalences, bounded ringFun and Frobenius maps are retained.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
boundary: Scene1/Derived; scalar and Tate-log transport, paper B/general E
identifications, and H1e/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittFrechetComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrechetFrobeniusComparison :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
private def originalRingEquivToCarrier := ringEquiv_toCarrier D w

set_option linter.defProp false in
private def carrierRingEquivNative (x : ActualCompleted D w) :
    carrierRingEquiv D w x =
      InitialThetaPadicWittAllRadiusComparison.NativeFunction.ringEquivFun D w
        (InitialThetaWittFrechetComparison.ringEquiv D w x) := rfl

set_option linter.defProp false in
private def ringEquivToCarrierNative (x : ActualCompleted D w) :=
  (originalRingEquivToCarrier D w x).trans (carrierRingEquivNative D w x)

set_option linter.defProp false in
def carrierRingEquiv_frobenius :=
  FrobeniusCompletionSquare.commutes
    (InitialThetaPadicWittAllRadiusComparison.ringEquiv_frobenius D w)
    (InitialThetaWittFrechetComparison.ringEquiv D w)
    id
    (carrierRingEquiv D w)
    (InitialThetaWittFrechetFrobenius.frobeniusEquiv D w)
    (PadicWittAllRadiusFrobenius.frobeniusEquiv (Arithmetic.residueChar w.1))
    (fun _ _ h => h)
    (InitialThetaWittFrechetFrobenius.frobeniusEquiv_apply D w)
    (fun _ => rfl)
    (carrierRingEquivNative D w)

set_option linter.defProp false in
def ringEquiv_frobenius :=
  FrobeniusCompletionSquare.commutes
    (InitialThetaPadicWittAllRadiusComparison.ringEquiv_frobenius D w)
    (InitialThetaWittFrechetComparison.ringEquiv D w)
    (PadicWittFrechetComparison.ringEquiv (Arithmetic.residueChar w.1))
    (ringEquiv D w)
    (InitialThetaWittFrechetFrobenius.frobeniusEquiv D w)
    (PadicWittFrechetFrobenius.frobeniusEquiv (Arithmetic.residueChar w.1))
    (PadicWittFrechetComparison.ringEquiv (Arithmetic.residueChar w.1)).injective
    (InitialThetaWittFrechetFrobenius.frobeniusEquiv_apply D w)
    (PadicWittFrechetFrobenius.frobeniusEquiv_apply (Arithmetic.residueChar w.1))
    (ringEquivToCarrierNative D w)

set_option linter.defProp false in
private def actualInverseRight :=
  (InitialThetaWittFrechetFrobenius.frobeniusEquiv D w).apply_symm_apply

set_option linter.defProp false in
private def standardInverseLeft (p : ℕ) [Fact p.Prime] :=
  (PadicWittFrechetFrobenius.frobeniusEquiv p).symm_apply_apply

set_option linter.defProp false in
def ringEquiv_inverseFrobenius :=
  Function.Semiconj.inverses_right (ringEquiv_frobenius D w)
    (actualInverseRight D w)
    (standardInverseLeft (Arithmetic.residueChar w.1))

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittFrechetComparison
