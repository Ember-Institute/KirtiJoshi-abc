import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittFrobeniusDictionaryCoherence
import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusPresentation

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FROBENIUS-RAW-PRESENTATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on the original bounded Witt localization and its denominator presentations.
fidelity: records the original standard Frobenius presentation law with the
same raw coefficient field and normed coefficient field instances as the
original standard Away quotient value law. The existing Ore recast supplies
the ring operation laws and integral inclusion law; its proved function
identity returns the conclusion to the original standard Frobenius function.
Uniqueness cancels the original denominator power, which is a unit.
All declarations depend only on p and its primality instance. The original
carriers, denominator, Frobenius function and numerator are retained. No
new map, norm, presentation hypothesis or comparison certificate is added.
Original proofs; no reference implementation copied. Prologue R5 retained.
boundary: Scene1/Derived; standard-side raw presentations only.
Actual-to-standard commutation, completion and the paper B, period and BK
identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.RawPresentation

open PadicBoundedWittLocalization.FrobeniusDictionaryCoherence
noncomputable section
variable (p : ℕ) [Fact p.Prime]

-- Cache the original source function before selecting the raw field dictionary.
private def originalWittFrobenius :
    PadicBoundedWittLocalization.Ainf p → PadicBoundedWittLocalization.Ainf p :=
  WittVector.frobenius

private theorem originalOreInclusion (a : PadicBoundedWittLocalization.Ainf p) :
    standardFrobeniusOre p (PadicBoundedWittLocalization.inclusion p a) =
      PadicBoundedWittLocalization.inclusion p (originalWittFrobenius p a) :=
  standardFrobeniusOre_inclusion_witt p a

private theorem rawIntegerCharP :
    (letI : Field (PadicTiltField.Carrier p) := FractionRing.field (PadicTiltField.Source p)
     letI : NormedField (PadicTiltField.Carrier p) := PadicTiltField.carrierNormedField p
     CharP (PadicTiltField.Integers p) p) := by
  have hcast : ∀ n : ℕ, (n : PadicTiltField.Integers p) = 0 ↔ p ∣ n :=
    CharP.cast_eq_zero_iff (PadicTiltField.Integers p) p
  letI : Field (PadicTiltField.Carrier p) := FractionRing.field (PadicTiltField.Source p)
  letI : NormedField (PadicTiltField.Carrier p) := PadicTiltField.carrierNormedField p
  exact ⟨hcast⟩

local instance rawCoefficientFieldFrobeniusPresentation : Field (PadicTiltField.Carrier p) :=
  FractionRing.field (PadicTiltField.Source p)
local instance normedCoefficientFieldFrobeniusPresentation :
    NormedField (PadicTiltField.Carrier p) :=
  PadicTiltField.carrierNormedField p
local instance rawIntegerCharPFrobeniusPresentation : CharP (PadicTiltField.Integers p) p :=
  rawIntegerCharP p

private theorem rawWittFrobenius_eq_original :
    (WittVector.frobenius :
      PadicBoundedWittLocalization.Ainf p → PadicBoundedWittLocalization.Ainf p) =
      originalWittFrobenius p := by
  rfl

theorem presentation_unique
    (y z : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (b : PadicBoundedWittLocalization.Ainf p)
    (hy : y * PadicBoundedWittLocalization.inclusion p
        (PadicBoundedWittLocalization.denominator p) ^ m =
      PadicBoundedWittLocalization.inclusion p b)
    (hz : z * PadicBoundedWittLocalization.inclusion p
        (PadicBoundedWittLocalization.denominator p) ^ m =
      PadicBoundedWittLocalization.inclusion p b) :
    y = z := by
  have hu : IsUnit
      (PadicBoundedWittLocalization.inclusion p
        (PadicBoundedWittLocalization.denominator p)) :=
    IsLocalization.Away.algebraMap_isUnit (PadicBoundedWittLocalization.denominator p)
  exact (hu.pow m).mul_right_cancel (hy.trans hz.symm)

theorem away_frobenius_presentation
    (x : PadicBoundedWittLocalization.Ring p) (m : ℕ)
    (a : PadicBoundedWittLocalization.Ainf p)
    (hx : x * PadicBoundedWittLocalization.inclusion p
        (PadicBoundedWittLocalization.denominator p) ^ m =
      PadicBoundedWittLocalization.inclusion p a) :
    PadicWittRhoFrobenius.frobeniusEquiv p x *
        PadicBoundedWittLocalization.inclusion p
          (PadicBoundedWittLocalization.denominator p) ^ (p * m) =
      PadicBoundedWittLocalization.inclusion p
        (WittFrobeniusPresentation.transform p m a) := by
  have hF : ∀ b : PadicBoundedWittLocalization.Ainf p,
      (standardFrobeniusOre p).toRingHom
          (algebraMap (PadicBoundedWittLocalization.Ainf p)
            (PadicBoundedWittLocalization.Ring p) b) =
        algebraMap (PadicBoundedWittLocalization.Ainf p)
          (PadicBoundedWittLocalization.Ring p) (WittVector.frobenius b) := by
    intro b
    exact (originalOreInclusion p b).trans
      (congrArg (PadicBoundedWittLocalization.inclusion p)
        (congrFun (rawWittFrobenius_eq_original p) b).symm)
  have h := WittFrobeniusPresentation.map_presentation p
    (PadicBoundedWittLocalization.contraction p) (standardFrobeniusOre p).toRingHom
    hF x m a hx
  exact (congrArg
    (fun y => y * PadicBoundedWittLocalization.inclusion p
      (PadicBoundedWittLocalization.denominator p) ^ (p * m))
    (standardFrobeniusOre_toFun p x)).symm.trans h

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobenius.RawPresentation
