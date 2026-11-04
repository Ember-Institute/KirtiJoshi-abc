import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLocalizationChoice
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrobeniusSource

/-!
source-id: JT-SCENE1-INITIAL-THETA-CHOICE-FROBENIUS-GENERIC-COMPARISON
source: Joshi II `se:ff-rings`, Frobenius on the localization of integral
Witt vectors at p and a contracting Teichmuller element; uniqueness of
localization lifts.
fidelity: identifies the full forward function of the original actual
choice Frobenius with the generic Witt-localization Frobenius. Both maps
use the original ChoiceRing, whose denominator is the original product of
p and the specified Teichmuller lift. The original inclusion law and source
Frobenius identity discharge uniqueness. No comparison certificate or
additional norm law is assumed. Original proof; no reference code copied.
boundary: actual choice carrier only; actual-to-standard naturality,
completion and paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeChoiceGenericComparison :
    Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem choiceFrobenius_inclusion_witt
    (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1)
    (a : InitialThetaTiltFontaine.Ainf D w) :
    choiceFrobenius D w s hs0 hs1 (algebraMap _ (ChoiceRing D w s) a) =
      algebraMap _ (ChoiceRing D w s) (WittVector.frobenius a) := by
  rw [choiceFrobenius_inclusion]
  exact congrArg (algebraMap (InitialThetaTiltFontaine.Ainf D w) (ChoiceRing D w s))
    (congrFun (InitialThetaBoundedWittLocalization.sourceFrobenius_eq_wittFrobenius D w) a)

-- Preserve the complete original-side instance specialization of uniqueness.
set_option linter.defProp false in
def choiceFrobenius_eq_genericHom
    (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) :=
  WittPrimeTeichFrobenius.hom_unique (Arithmetic.residueChar w.1) s
    (choiceFrobenius D w s hs0 hs1).toRingHom
    (choiceFrobenius_inclusion_witt D w s hs0 hs1)

-- Equality of full forward functions, with no new expected ring-map type.
set_option linter.defProp false in
def choiceFrobenius_toFun_eq_genericHom
    (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) :=
  congrArg DFunLike.coe (choiceFrobenius_eq_genericHom D w s hs0 hs1)

end
end JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice
