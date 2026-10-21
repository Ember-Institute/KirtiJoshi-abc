import ArithmeticTeichmullerSpaces.Prologue.Interfaces.PerfectoidBridge
import ArithmeticTeichmullerSpaces.Prologue.Interfaces.Contracts
import ArithmeticTeichmullerSpaces.Prologue.Theta.Tate

namespace JoshiTeich.Prologue

universe uK

/-!
The Prologue input bundle joins the number-field theta-link data to one
explicit local Perfectoid bridge.  It is a data carrier only; no Corollary
3.12 or downstream volume estimate is hidden in this structure.
-/

structure PrologueInputData (K : Type uK) [Field K] [NumberField K]
    (O : Type uK) [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  link : AdelicThetaLinkData K
  placeData : PerfectoidPlaceData K O p
  bridge : PerfectoidBridgeData link p placeData

structure PrologueInputLaws {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (X : PrologueInputData K O p) : Prop where
  first_axiom : FirstAxiom X.link
  tate_parameter : Theta.TateParameterLaws X.link.tate
  perfectoid_bridge : PerfectoidBridgeLaws X.link p X.placeData X.bridge

end JoshiTeich.Prologue
