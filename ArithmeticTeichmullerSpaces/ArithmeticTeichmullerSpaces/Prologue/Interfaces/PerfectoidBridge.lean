import ArithmeticTeichmullerSpaces.Prologue.Interfaces.Carriers
import ArithmeticTeichmullerSpaces.Prologue.Perfectoid.Data

namespace JoshiTeich.Prologue

universe uK

open scoped NumberField

/-!
This boundary records the type-level relationship between a number-field
finite place and a local perfectoid input.  The local ring, prime parameter,
and all required instances are explicit fields; no global instance is used to
silently identify the two sides.
-/

structure PerfectoidPlaceData (K : Type uK) [Field K] [NumberField K]
    (O : Type uK) [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  place : NumberField.FinitePlace K
  data : Perfectoid.PerfectoidData (O := O) (p := p)

structure PerfectoidPlaceLaws {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (P : PerfectoidPlaceData K O p) : Prop where
  perfectoid : Perfectoid.PerfectoidLaws P.data

structure PerfectoidBridgeData {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K) {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (P : PerfectoidPlaceData K O p) where
  coefficientMap : 𝓞 K →+* O

structure PerfectoidBridgeLaws {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K) {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (P : PerfectoidPlaceData K O p)
    (B : PerfectoidBridgeData D p P) : Prop where
  place_supported : P.place ∈ D.places
  local_laws : PerfectoidPlaceLaws p P

end JoshiTeich.Prologue
