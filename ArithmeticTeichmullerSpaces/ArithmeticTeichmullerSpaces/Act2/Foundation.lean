import ArithmeticTeichmullerSpaces.Foundations.Carriers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

namespace JoshiTeich

open scoped BigOperators

/-!
`AST₀` is the first public assumption. It contains structural properties of
the carriers and deliberately contains no Corollary 3.12 inequality.
-/

def AST₀ (D : ASTData) : Prop :=
  letI := D.fieldStructure
  Nat.Prime D.ell ∧
    D.ell % 2 = 1 ∧
    D.ellStar = (D.ell - 1) / 2 ∧
    D.ossPlaces.Nonempty ∧
    (∀ w ∈ D.ossPlaces, 0 < (D.place w).residueDegree) ∧
    (∀ w ∈ D.ossPlaces, ∃ x : D.K, (D.place w).valuation x ≠ 0) ∧
    D.theta.qParameter ≠ 0 ∧
    (∀ w ∈ D.ossPlaces, 0 < D.qNorm w) ∧
    (∀ x, 0 ≤ D.norm x) ∧
    (∀ x, 0 ≤ D.height x) ∧
    D.packet.packetIndex ⊆ D.theta.thetaPilot

/-!
`FirstAxiom` is a separate interface. Its fields are intentionally
redundant with the eventual `AST₀` proof: this keeps the public theorem
parameters explicit and lets Act2 prove each interface independently.
-/
structure FirstAxiom (D : ASTData) : Prop where
  ell_prime : Nat.Prime D.ell
  ell_odd : D.ell % 2 = 1
  ell_star : D.ellStar = (D.ell - 1) / 2
  oss_nonempty : D.ossPlaces.Nonempty
  place_degree_pos : ∀ w ∈ D.ossPlaces, 0 < (D.place w).residueDegree
  valuation_nontrivial : ∀ w ∈ D.ossPlaces, ∃ x : D.K, (D.place w).valuation x ≠ 0
  q_parameter_nonzero : letI := D.fieldStructure; D.theta.qParameter ≠ 0
  q_norm_pos : ∀ w ∈ D.ossPlaces, 0 < D.qNorm w
  norm_nonnegative : ∀ x, 0 ≤ D.norm x
  height_nonnegative : ∀ x, 0 ≤ D.height x
  packet_supported : D.packet.packetIndex ⊆ D.theta.thetaPilot

/-!
This is the target proposition for the public Corollary 3.12 interface. The
local `q` norms and the log-volume are data fields, while the inequality is
kept here as a proposition to be proved later from explicit contracts.
-/
def Corollary312 (D : ASTData) : Prop :=
  letI := D.fieldStructure
  let localTerm : ℕ → ℝ := fun w =>
    Real.log (Real.rpow (D.qNorm w) (1 / (2 * (D.ell : ℝ))))
  let total : ℝ := Finset.sum D.ossPlaces localTerm
  0 - total ≤ -((1 : ℝ) / (D.ellStar : ℝ)) * abs (Real.log D.packet.logVolume)

end JoshiTeich
