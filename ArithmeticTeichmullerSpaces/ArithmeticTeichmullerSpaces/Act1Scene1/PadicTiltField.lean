import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltAlgebraicallyClosed
import Mathlib.NumberTheory.Padics.Complex

/-!
source-id: JT-SCENE1-STANDARD-PADIC-TILT-FIELD
source: Joshi II `se:ff-rings`, with fixed F=C_p^flat;
Mathlib's standard C_p and the proved geometric tilt constructions.
fidelity: constructs the standard C_p pretilt and its original fraction
field using only p. Its norm is the original tilt valuation; completeness,
algebraic closedness, characteristic p, perfectness and nontriviality are
proved from standard C_p. No InitialThetaData or comparison certificate
is input, and no closure replaces the tilt carrier. Original proofs.
boundary: Scene1/Derived; period-ring and paper B identities remain open.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicTiltField

open scoped NNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

theorem norm_prime : ‖(p : PadicComplex p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicComplex p)) p, norm_algebraMap', Padic.norm_p]

instance primeNormFact : Fact (0 < ‖(p : PadicComplex p)‖ ∧ ‖(p : PadicComplex p)‖ < 1) := by
  constructor
  rw [norm_prime]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact ⟨inv_pos.mpr (zero_lt_one.trans hp), inv_lt_one_of_one_lt₀ hp⟩

abbrev Source := GeometricTiltField.Source (PadicComplex p) p
abbrev Carrier := GeometricTiltField.FractionField (PadicComplex p) p

instance carrierNormedField : NormedField (Carrier p) :=
  GeometricTiltNorm.fractionNormedField (PadicComplex p) p

instance carrierUniformSpace : UniformSpace (Carrier p) :=
  (inferInstance : PseudoMetricSpace (Carrier p)).toUniformSpace

instance carrierTopologicalSpace : TopologicalSpace (Carrier p) :=
  (carrierUniformSpace p).toTopologicalSpace

instance carrierCharP : CharP (Carrier p) p :=
  GeometricTiltField.fractionField_charP (PadicComplex p) p

instance carrierPerfect : PerfectRing (Carrier p) p :=
  GeometricTiltField.fractionField_perfect (PadicComplex p) p

theorem norm_eq_valuation (x : Carrier p) :
    ‖x‖ = (GeometricTiltField.fractionValuation (PadicComplex p) p x : ℝ) := rfl

theorem nnnorm_eq_valuation (x : Carrier p) :
    ‖x‖₊ = GeometricTiltField.fractionValuation (PadicComplex p) p x := Subtype.ext rfl

instance carrierUltrametric : IsUltrametricDist (Carrier p) :=
  GeometricTiltNorm.fractionUltrametric (PadicComplex p) p

instance carrierCompleteSpace : CompleteSpace (Carrier p) :=
  GeometricTiltCompleteness.fractionCompleteSpace (PadicComplex p) p

instance carrierIsAlgClosed : IsAlgClosed (Carrier p) :=
  GeometricTiltAlgebraicallyClosed.fractionIsAlgClosed (PadicComplex p) p

theorem exists_contracting : ∃ t : Carrier p, 0 < ‖t‖ ∧ ‖t‖ < 1 :=
  GeometricTiltAlgebraicallyClosed.exists_contracting (PadicComplex p) p

instance carrierNontriviallyNormedField : NontriviallyNormedField (Carrier p) where
  toNormedField := carrierNormedField p
  non_trivial := by
    obtain ⟨t, ht0, ht1⟩ := exists_contracting p
    refine ⟨t⁻¹, ?_⟩
    rw [norm_inv]
    exact (one_lt_inv₀ ht0).mpr ht1

instance carrierValued : Valued (Carrier p) ℝ≥0 := NormedField.toValued

theorem valued_eq_fractionValuation :
    (Valued.v : Valuation (Carrier p) ℝ≥0) =
      GeometricTiltField.fractionValuation (PadicComplex p) p := by
  ext x
  exact congrArg (fun r : ℝ≥0 => (r : ℝ)) (nnnorm_eq_valuation p x)

instance valuationRankOne :
    Valuation.RankOne (GeometricTiltField.fractionValuation (PadicComplex p) p) := by
  rw [← valued_eq_fractionValuation]
  exact inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := Carrier p)))

abbrev Integers := LocalGeometricFontaine.integerRing (Carrier p)

end
end JoshiTeich.Act1Scene1.PadicTiltField
