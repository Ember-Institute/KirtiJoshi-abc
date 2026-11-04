import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittLocalization

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FROBENIUS-SOURCE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the original
Witt Frobenius on the initial-theta bounded localization source.
fidelity: records the full forward-function equality between the existing
source Frobenius and Witt Frobenius, its existing localization inclusion
law, and the forward function of the existing localization equivalence.
It uses the original AG, TG, D and w context and the selected residue prime.
The original functions, rings and inclusions are unchanged.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; actual-to-standard comparison and paper B marking,
period and BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittLocalization

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeFrobeniusSource : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem sourceFrobenius_eq_wittFrobenius :
    (sourceFrobenius D w :
      InitialThetaTiltFontaine.Ainf D w → InitialThetaTiltFontaine.Ainf D w) =
      WittVector.frobenius := rfl

theorem frobenius_inclusion_witt (a : InitialThetaTiltFontaine.Ainf D w) :
    frobenius D w (inclusion D w a) =
      inclusion D w (WittVector.frobenius a) :=
  frobenius_inclusion D w a

theorem frobeniusEquiv_eq_frobenius :
    (frobeniusEquiv D w : Ring D w → Ring D w) =
      (frobenius D w : Ring D w → Ring D w) := rfl

theorem frobeniusEquiv_inclusion_witt (a : InitialThetaTiltFontaine.Ainf D w) :
    frobeniusEquiv D w (InitialThetaBoundedWittLocalization.inclusion D w a) =
      InitialThetaBoundedWittLocalization.inclusion D w (WittVector.frobenius a) := by
  change frobenius D w (InitialThetaBoundedWittLocalization.inclusion D w a) = _
  exact frobenius_inclusion_witt D w a

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittLocalization
