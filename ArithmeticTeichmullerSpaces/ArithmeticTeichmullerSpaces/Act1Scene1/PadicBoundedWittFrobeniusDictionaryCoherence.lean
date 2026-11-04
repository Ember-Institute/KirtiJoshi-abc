import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalizationFrobeniusRecast
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrobeniusSource

/-!
source-id: JT-SCENE1-PADIC-BOUNDED-WITT-FROBENIUS-DICTIONARY-COHERENCE
source: Joshi II `se:ff-rings`; the original standard p-only bounded Witt
localization and its standard C_p^flat coefficient ring.
fidelity: proves that the original Ore-localization multiplication and
addition dictionaries agree with the dictionaries induced by the existing
standard bounded ring structure. The Ore and normed-field paths use the same
original carrier. No carrier, map, or ring instance is replaced downstream.
The original standard Frobenius forward function preserves the raw Ore one
and multiplication, as follows from the recast equivalence's operation laws
and its exact forward-function identity.
Original proof; no reference implementation copied. Prologue R5 retained.
boundary: p-only operation coherence; no actual comparison or paper B
identity is established here.
-/

namespace JoshiTeich.Act1Scene1.PadicBoundedWittLocalization.FrobeniusDictionaryCoherence

noncomputable section
set_option warn.classDefReducibility false

variable (p : ℕ) [Fact p.Prime]

def oreCarrierCommRing : CommRing (PadicTiltField.Carrier p) :=
  @OreLocalization.instCommRing
    (PadicTiltField.Source p)
    (inferInstance : CommRing (PadicTiltField.Source p))
    (nonZeroDivisors (PadicTiltField.Source p))
    inferInstance

def oreIntegerCommRing : CommRing (PadicTiltField.Integers p) :=
  @Subring.toCommRing (PadicTiltField.Carrier p) (oreCarrierCommRing p)
    (PadicTiltField.Integers p)

def oreWittCommRing : CommRing (WittVector p (PadicTiltField.Integers p)) :=
  letI : CommRing (PadicTiltField.Integers p) := oreIntegerCommRing p
  inferInstance

def oreBoundedCommRing : CommRing (PadicBoundedWittLocalization.Ring p) :=
  letI : CommRing (PadicTiltField.Integers p) := oreIntegerCommRing p
  letI : CommRing (WittVector p (PadicTiltField.Integers p)) := oreWittCommRing p
  let S : Submonoid (WittVector p (PadicTiltField.Integers p)) :=
    Submonoid.powers (WittPrimeTeichLocalization.denominator p
      (PadicBoundedWittLocalization.contraction p))
  @OreLocalization.instCommRing
    (WittVector p (PadicTiltField.Integers p))
    (oreWittCommRing p) S inferInstance

def standardBoundedCommRing : CommRing (PadicBoundedWittLocalization.Ring p) :=
  inferInstance

theorem targetMul_eq :
    LocalizationFrobeniusNaturality.commRingMul (oreBoundedCommRing p) =
      LocalizationFrobeniusNaturality.commRingMul (standardBoundedCommRing p) := by
  rfl

theorem targetAdd_eq :
    LocalizationFrobeniusNaturality.commRingAdd (oreBoundedCommRing p) =
      LocalizationFrobeniusNaturality.commRingAdd (standardBoundedCommRing p) := by
  rfl

-- Recast the existing standard Frobenius to the raw Ore dictionary.
def standardFrobeniusOre :
    @RingEquiv (PadicBoundedWittLocalization.Ring p)
      (PadicBoundedWittLocalization.Ring p)
      (LocalizationFrobeniusNaturality.commRingMul (oreBoundedCommRing p))
      (LocalizationFrobeniusNaturality.commRingMul (oreBoundedCommRing p))
      (LocalizationFrobeniusNaturality.commRingAdd (oreBoundedCommRing p))
      (LocalizationFrobeniusNaturality.commRingAdd (oreBoundedCommRing p)) :=
  RingEquivDictionaryTransport.recast
    (PadicWittRhoFrobenius.frobeniusEquiv p)
    (targetMul_eq p).symm (targetMul_eq p).symm
    (targetAdd_eq p).symm (targetAdd_eq p).symm

theorem standardFrobeniusOre_toFun (x : PadicBoundedWittLocalization.Ring p) :
    @Equiv.toFun (PadicBoundedWittLocalization.Ring p)
        (PadicBoundedWittLocalization.Ring p)
        (@RingEquiv.toEquiv (PadicBoundedWittLocalization.Ring p)
          (PadicBoundedWittLocalization.Ring p)
          (LocalizationFrobeniusNaturality.commRingMul (oreBoundedCommRing p))
          (LocalizationFrobeniusNaturality.commRingMul (oreBoundedCommRing p))
          (LocalizationFrobeniusNaturality.commRingAdd (oreBoundedCommRing p))
          (LocalizationFrobeniusNaturality.commRingAdd (oreBoundedCommRing p))
          (standardFrobeniusOre p)) x =
      PadicWittRhoFrobenius.frobeniusEquiv p x := by
  exact congrFun
    (RingEquivDictionaryTransport.recast_toFun
      (PadicWittRhoFrobenius.frobeniusEquiv p)
      (targetMul_eq p).symm (targetMul_eq p).symm
      (targetAdd_eq p).symm (targetAdd_eq p).symm) x

theorem standardFrobeniusOre_inclusion_witt
    (a : PadicBoundedWittLocalization.Ainf p) :
    standardFrobeniusOre p (PadicBoundedWittLocalization.inclusion p a) =
      PadicBoundedWittLocalization.inclusion p (WittVector.frobenius a) := by
  calc
    standardFrobeniusOre p (PadicBoundedWittLocalization.inclusion p a) =
        PadicWittRhoFrobenius.frobeniusEquiv p
          (PadicBoundedWittLocalization.inclusion p a) :=
      standardFrobeniusOre_toFun p _
    _ = PadicBoundedWittLocalization.inclusion p (WittVector.frobenius a) :=
      PadicWittRhoFrobenius.frobeniusEquiv_inclusion_witt p a

-- Select the original raw Ore operations explicitly.
def oreOne : PadicBoundedWittLocalization.Ring p :=
  letI : CommRing (PadicBoundedWittLocalization.Ring p) := oreBoundedCommRing p
  1

def oreMul (x y : PadicBoundedWittLocalization.Ring p) :
    PadicBoundedWittLocalization.Ring p :=
  @Mul.mul (PadicBoundedWittLocalization.Ring p)
    (LocalizationFrobeniusNaturality.commRingMul (oreBoundedCommRing p)) x y

theorem frobeniusEquiv_map_oreOne :
    (PadicWittRhoFrobenius.frobeniusEquiv p).toEquiv.toFun (oreOne p) =
      oreOne p := by
  letI : CommRing (PadicBoundedWittLocalization.Ring p) := oreBoundedCommRing p
  have h := (standardFrobeniusOre p).map_one
  change standardFrobeniusOre p (oreOne p) = oreOne p at h
  exact (standardFrobeniusOre_toFun p (oreOne p)).symm.trans h

theorem frobeniusEquiv_map_oreMul (x y : PadicBoundedWittLocalization.Ring p) :
    (PadicWittRhoFrobenius.frobeniusEquiv p).toEquiv.toFun (oreMul p x y) =
      oreMul p
        ((PadicWittRhoFrobenius.frobeniusEquiv p).toEquiv.toFun x)
        ((PadicWittRhoFrobenius.frobeniusEquiv p).toEquiv.toFun y) := by
  letI : CommRing (PadicBoundedWittLocalization.Ring p) := oreBoundedCommRing p
  have h := (standardFrobeniusOre p).map_mul x y
  change standardFrobeniusOre p (oreMul p x y) =
    oreMul p (standardFrobeniusOre p x) (standardFrobeniusOre p y) at h
  exact (standardFrobeniusOre_toFun p (oreMul p x y)).symm.trans
    (h.trans (congrArg₂ (oreMul p) (standardFrobeniusOre_toFun p x)
      (standardFrobeniusOre_toFun p y)))

end
end JoshiTeich.Act1Scene1.PadicBoundedWittLocalization.FrobeniusDictionaryCoherence
