import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FROBENIUS-RING-COMPOSITION
source: Joshi II `se:ff-rings`, change of contracting Teichmuller element
and the original actual-to-standard bounded Witt localization comparison.
fidelity: records the full function of the original bounded ring
equivalence as the choice comparison composed with the inverse choice
equivalence. The identity uses the original definition directly, without
an intermediate saved-function wrapper. No map, carrier, operation
instance or comparison law is changed. Original proof; no reference
implementation copied. Prologue R5 retained.
boundary: definition identity only; Frobenius naturality, completion
and paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrobeniusRingComposition :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem choiceComposition_eq_ringEquivFunction :
    choiceStandardFun D w ∘ (choiceEquiv D w).symm.toEquiv.toFun =
      (ringEquiv D w).toEquiv.toFun := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
