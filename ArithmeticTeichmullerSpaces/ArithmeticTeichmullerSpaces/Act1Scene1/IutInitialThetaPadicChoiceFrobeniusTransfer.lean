import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrobeniusUnifiedNaturality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaChoiceNativeConjugation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittFrobeniusRingComposition
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusNativeFunction


/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-CHOICE-FROBENIUS-TRANSFER
source: Joshi II `se:ff-rings`, Frobenius under a change of contracting
Teichmuller element and the original actual-to-standard bounded comparison.
fidelity: transfers the proved choice-to-standard naturality law directly
to the original canonical bounded comparison function. The choice action,
actual action, target action and comparison function have the original
concrete carriers in the theorem telescope. The proof uses the original
choice conjugation and original comparison composition identities. No
RingEquiv dictionary recast, carrier replacement, norm law or new source
assumption is introduced. Original proof; no reference implementation copied.
boundary: bounded algebraic naturality only; completion and paper B, period
and BK identities remain separate. Prologue R5 retained.
-/
namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceFrobeniusTransfer :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

set_option linter.defProp false in
private theorem canonicalLeftStep
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (ringEquiv D w).toEquiv.toFun
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) =
      choiceStandardFun D w
        ((choiceEquiv D w).symm.toEquiv.toFun
          (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x)) := by
  exact (congrFun (choiceComposition_eq_ringEquivFunction D w)
    (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x)).symm

set_option linter.defProp false in
private theorem canonicalChoiceActionStep
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    choiceStandardFun D w
        (InitialThetaWittLocalizationChoice.NativeFunction.frobeniusFun
          D w (contraction D w) (contraction_ne_zero D w)
          (contraction_norm_lt_one D w)
          ((choiceEquiv D w).symm.toEquiv.toFun x)) =
      choiceStandardFun D w
        ((choiceEquiv D w).symm.toEquiv.toFun
          (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x)) := by
  apply congrArg (choiceStandardFun D w)
  have hq := InitialThetaWittLocalizationChoice.NativeFunction.frobeniusFun_eq_conjugate
    D w (contraction D w) (contraction_ne_zero D w) (contraction_norm_lt_one D w)
  calc
    _ = (choiceEquiv D w).symm.toEquiv.toFun
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w
          ((choiceEquiv D w).toEquiv
            ((choiceEquiv D w).symm.toEquiv.toFun x))) :=
      congrFun hq ((choiceEquiv D w).symm.toEquiv.toFun x)
    _ = (choiceEquiv D w).symm.toEquiv.toFun
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) :=
      congrArg
        (fun y => (choiceEquiv D w).symm.toEquiv.toFun
          (InitialThetaBoundedWittLocalization.frobeniusEquiv D w y))
        ((choiceEquiv D w).apply_symm_apply x)

set_option linter.defProp false in
private theorem canonicalChoiceNaturalityStep
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    choiceStandardFun D w
        (InitialThetaWittLocalizationChoice.NativeFunction.frobeniusFun
          D w (contraction D w) (contraction_ne_zero D w)
          (contraction_norm_lt_one D w)
          ((choiceEquiv D w).symm.toEquiv.toFun x)) =
      PadicWittRhoFrobenius.NativeFunction.frobeniusFun
        (Arithmetic.residueChar w.1)
        (choiceStandardFun D w
          ((choiceEquiv D w).symm.toEquiv.toFun x)) :=
  InitialThetaPadicWittFrobeniusUnifiedNaturality.choiceFrobeniusNaturality D w
    ((choiceEquiv D w).symm.toEquiv.toFun x)

set_option linter.defProp false in
private theorem canonicalRightStep
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    PadicWittRhoFrobenius.NativeFunction.frobeniusFun
        (Arithmetic.residueChar w.1)
        (choiceStandardFun D w
          ((choiceEquiv D w).symm.toEquiv.toFun x)) =
      PadicWittRhoFrobenius.NativeFunction.frobeniusFun
        (Arithmetic.residueChar w.1)
        ((ringEquiv D w).toEquiv.toFun x) := by
  exact congrArg (PadicWittRhoFrobenius.NativeFunction.frobeniusFun
    (Arithmetic.residueChar w.1))
    (congrFun (choiceComposition_eq_ringEquivFunction D w) x)

set_option linter.defProp false in
def canonicalFrobeniusNaturality
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (ringEquiv D w).toEquiv.toFun
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) =
      PadicWittRhoFrobenius.NativeFunction.frobeniusFun
        (Arithmetic.residueChar w.1)
        ((ringEquiv D w).toEquiv.toFun x) :=
    (canonicalLeftStep D w x).trans
      ((canonicalChoiceActionStep D w x).symm.trans
        ((canonicalChoiceNaturalityStep D w x).trans (canonicalRightStep D w x)))

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
