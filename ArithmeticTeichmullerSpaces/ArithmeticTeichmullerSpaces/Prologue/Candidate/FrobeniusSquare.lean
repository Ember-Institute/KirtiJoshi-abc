import ArithmeticTeichmullerSpaces.Prologue.Interfaces.Carriers

namespace JoshiTeich.Prologue.Candidate

variable {K : Type*} [Field K] [NumberField K]

/-!
source-id: JT-ATS-CANDIDATE-FROBENIUS-SQUARE-NORM
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`th:adelic-theta-link` (1139--1166), especially the `j^2` valuation scaling
and Frobenius stability statements
fidelity: rejected reinterpretation; the paper does not state this norm law
boundary: Prologue/Candidate; this module is never imported by Interfaces or Scene1

This candidate records the stronger reading that was previously placed in the
Core contract.  It is retained only so the rejection can be audited by an
explicit counter-consequence.  The sourced `ThetaPilotScalingLaws` relation
remains the Core representation of the `j^2` scaling.
-/

structure FrobeniusSquareNormLaw (D : AdelicThetaLinkData K) : Prop where
  norm_square : ∀ i, D.theta.norm (D.theta.frobenius i) = D.theta.norm i ^ 2

end JoshiTeich.Prologue.Candidate
