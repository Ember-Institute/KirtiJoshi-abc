import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltCompleteness

/-!
source-id: JT-SCENE1-GEOMETRIC-TILT-INTEGER-RING
source: Joshi II `se:ff-rings`, using the proved PreTilt unit-ball
description and Mathlib valuation integer rings.
fidelity: identifies the original integral PreTilt with the valuation
integer ring of its original fraction field. The construction keeps the
fraction carrier and its valuation norm. It does not construct a Witt,
bounded-localization, rho, Frechet, or paper `B` comparison.
Original proof; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricTiltIntegerRing

open JoshiTeich.Prologue
open GeometricTiltField
noncomputable section
universe u
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω]
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]
variable [CompleteSpace Ω] [IsAlgClosed Ω]

local instance normedFractionField : NormedField (GeometricTiltField.FractionField Ω p) :=
  GeometricTiltNorm.fractionNormedField Ω p

local instance ultrametricFractionField : IsUltrametricDist
    (GeometricTiltField.FractionField Ω p) :=
  GeometricTiltNorm.fractionUltrametric Ω p

abbrev FractionIntegers :=
  LocalGeometricFontaine.integerRing (GeometricTiltField.FractionField Ω p)

def preTiltEquiv : GeometricTiltField.Source Ω p ≃+* FractionIntegers Ω p :=
  RingEquiv.ofBijective
    ((algebraMap (GeometricTiltField.Source Ω p)
      (GeometricTiltField.FractionField Ω p)).codRestrict _ (fun x => by
        apply (LocalGeometricFontaine.mem_integerRing
          (GeometricTiltField.FractionField Ω p) _).mpr
        rw [GeometricTiltNorm.inclusion_norm]
        exact GeometricTiltCompleteness.source_norm_le_one Ω p x))
    ⟨(by
      intro x y h
      exact IsFractionRing.injective (GeometricTiltField.Source Ω p)
        (GeometricTiltField.FractionField Ω p)
        (congrArg Subtype.val h)), (by
      intro x
      have hx : ‖(x : GeometricTiltField.FractionField Ω p)‖ ≤ 1 :=
        (LocalGeometricFontaine.mem_integerRing
          (GeometricTiltField.FractionField Ω p) _).mp x.property
      obtain ⟨a, ha⟩ := GeometricTiltCompleteness.norm_le_one_mem_range Ω p
        (x : GeometricTiltField.FractionField Ω p) hx
      exact ⟨a, Subtype.ext ha⟩)⟩

theorem preTiltEquiv_apply (x : GeometricTiltField.Source Ω p) :
    (preTiltEquiv Ω p x : GeometricTiltField.FractionField Ω p) =
      algebraMap (GeometricTiltField.Source Ω p)
        (GeometricTiltField.FractionField Ω p) x := rfl

theorem preTiltEquiv_norm (x : GeometricTiltField.Source Ω p) :
    ‖preTiltEquiv Ω p x‖ = ‖x‖ := by
  exact GeometricTiltNorm.inclusion_norm Ω p x

end
end JoshiTeich.Act1Scene1.GeometricTiltIntegerRing
