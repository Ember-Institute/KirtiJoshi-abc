import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltCompleteness

/-!
source-id: JT-SCENE1-GEOMETRIC-TILT-NORM
source: Joshi II `se:ff-rings` and the original tilt valuation on the
fraction field of the actual integral PreTilt.
fidelity: turns that same valuation into a real absolute value and an
explicit normed-field structure. The original PreTilt inclusion preserves
the norm and has closed, complete image. No norm or topology law is input.
The normed-field structure is a definition for local use, so existing
actual tilt norm instances remain available. Original proofs.
boundary: Scene1/Derived; completeness of the full fraction field and
algebraic closedness are separate results. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricTiltNorm

open scoped NNReal Topology
noncomputable section
universe u
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω]
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

theorem fractionValuation_eq_zero_iff (x : GeometricTiltField.FractionField Ω p) :
    GeometricTiltField.fractionValuation Ω p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hh : (0 : ℝ≥0) = 1 := calc
      0 = GeometricTiltField.fractionValuation Ω p x *
          GeometricTiltField.fractionValuation Ω p x⁻¹ := by rw [h, zero_mul]
      _ = GeometricTiltField.fractionValuation Ω p (x * x⁻¹) :=
        (map_mul (GeometricTiltField.fractionValuation Ω p) x x⁻¹).symm
      _ = 1 := by rw [mul_inv_cancel₀ hx, map_one]
    exact zero_ne_one hh
  · rintro rfl
    exact map_zero _

/-- The real absolute value is the original fraction valuation. -/
def absoluteValue : AbsoluteValue (GeometricTiltField.FractionField Ω p) ℝ where
  toFun x := GeometricTiltField.fractionValuation Ω p x
  map_mul' x y := by
    exact_mod_cast map_mul (GeometricTiltField.fractionValuation Ω p) x y
  nonneg' x := (GeometricTiltField.fractionValuation Ω p x).property
  eq_zero' x := by
    rw [NNReal.coe_eq_zero]
    exact fractionValuation_eq_zero_iff Ω p x
  add_le' x y :=
    (NNReal.coe_le_coe.mpr ((GeometricTiltField.fractionValuation Ω p).map_add x y)).trans
      (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

/-- Consumers install this structure locally on the original fraction field. -/
@[instance_reducible]
def fractionNormedField : NormedField (GeometricTiltField.FractionField Ω p) :=
  (absoluteValue Ω p).toNormedField

local instance localFractionNormedField : NormedField (GeometricTiltField.FractionField Ω p) :=
  fractionNormedField Ω p

theorem norm_eq_valuation (x : GeometricTiltField.FractionField Ω p) :
    ‖x‖ = (GeometricTiltField.fractionValuation Ω p x : ℝ) := rfl

theorem nnnorm_eq_valuation (x : GeometricTiltField.FractionField Ω p) :
    ‖x‖₊ = GeometricTiltField.fractionValuation Ω p x := Subtype.ext rfl

/-- The explicit fraction-field norm has the original ultrametric inequality. -/
theorem fractionUltrametric : IsUltrametricDist (GeometricTiltField.FractionField Ω p) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  change (GeometricTiltField.fractionValuation Ω p (x + y) : ℝ) ≤ _
  exact_mod_cast (GeometricTiltField.fractionValuation Ω p).map_add x y

section CompleteSource
variable [CompleteSpace Ω]

local instance localSourceNormedRing : NormedRing (GeometricTiltField.Source Ω p) :=
  GeometricPreTiltCompleteness.sourceNormedRing Ω p

local instance localSourceCompleteSpace : CompleteSpace (GeometricTiltField.Source Ω p) :=
  GeometricPreTiltCompleteness.sourceCompleteSpace Ω p

theorem inclusion_norm (x : GeometricTiltField.Source Ω p) :
    ‖algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) x‖ =
      ‖x‖ := by
  rw [norm_eq_valuation, GeometricTiltField.fractionValuation_inclusion,
    GeometricPreTiltCompleteness.norm_eq_valuation]

theorem inclusion_isometry :
    Isometry (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p)) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, ← map_sub
    (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p)) x y,
    inclusion_norm, dist_eq_norm]

theorem inclusion_range_isClosed :
    IsClosed (Set.range
      (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p))) :=
  (inclusion_isometry Ω p).isClosedEmbedding.isClosed_range

theorem inclusion_range_isComplete :
    IsComplete (Set.range
      (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p))) :=
  (inclusion_isometry Ω p).isUniformInducing.isComplete_range

end CompleteSource
end
end JoshiTeich.Act1Scene1.GeometricTiltNorm
