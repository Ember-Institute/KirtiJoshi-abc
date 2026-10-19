import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltDivision
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPreTiltCompleteness

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-COMPLETENESS
source: Joshi Arithmetic Holomorphic Structures tilt after lem:perfectoid;
actual coefficient inverse limit, closed PreTilt inclusion and division
approximations. Original proofs; no reference source code copied.
fidelity: identifies the original PreTilt image with the original tilt's
closed unit ball, then proves the same field complete. No completion replaces
its carrier and no valuation-ring/completeness certificate is input.
Algebraic closedness and a selected holomorphoid identity remain open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltCompleteness

open JoshiTeich.Prologue Filter
open scoped NNReal Topology
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

/-- This is the actual fraction-field representation of the existing tilt carrier. -/
theorem fraction_representation (x : InitialThetaTiltField.Carrier D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    ∃ a b : InitialThetaTiltField.Source D w, b ≠ 0 ∧
      InitialThetaTiltField.inclusion D w a / InitialThetaTiltField.inclusion D w b = x := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective
    (GeometricTiltField.Source (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
      (Arithmetic.residueChar w.1))
    (show GeometricTiltField.FractionField (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
      (Arithmetic.residueChar w.1) from x)
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, hx⟩

theorem source_norm_le_one (a : InitialThetaTiltField.Source D w) : ‖a‖ ≤ 1 := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [InitialThetaPreTiltCompleteness.norm_eq_sourceValuation, ← InitialThetaTiltSharp.untilt_norm]
  exact (LocalGeometricFontaine.mem_integerRing _ _).mp
    ((InitialThetaCanonicalGeometricFontaine.placeData D w).data.untilt a).property

/-- Each integral fraction can be approximated to arbitrary precision inside the actual PreTilt. -/
theorem integral_fraction_mem_closure (a b : InitialThetaTiltField.Source D w) (hb : b ≠ 0)
    (hab : ‖a‖ ≤ ‖b‖) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    InitialThetaTiltField.inclusion D w a / InitialThetaTiltField.inclusion D w b ∈
      closure (Set.range (InitialThetaTiltField.inclusion D w)) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hb' : InitialThetaTiltField.inclusion D w b ≠ 0 := by
    intro h
    exact hb ((InitialThetaTiltField.inclusion_injective D w) (h.trans (map_zero _).symm))
  have hbn : 0 < ‖InitialThetaTiltField.inclusion D w b‖ := norm_pos_iff.mpr hb'
  obtain ⟨n, hn⟩ := GeometricPreTiltCompleteness.exists_coeffRadius_lt
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1)
      (ε * ‖InitialThetaTiltField.inclusion D w b‖) (mul_pos hε hbn)
  let c := GeometricPreTiltDivision.approximation
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1)
      a b hb hab n
  refine ⟨InitialThetaTiltField.inclusion D w c, ⟨c, rfl⟩, ?_⟩
  have herr := GeometricPreTiltDivision.approximation_error_norm
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1)
      a b hb hab n
  have heq : InitialThetaTiltField.inclusion D w a / InitialThetaTiltField.inclusion D w b -
      InitialThetaTiltField.inclusion D w c =
        InitialThetaTiltField.inclusion D w (a - b * c) / InitialThetaTiltField.inclusion D w b := by
    rw [map_sub, map_mul]
    field_simp
  rw [dist_eq_norm, heq, norm_div, InitialThetaPreTiltCompleteness.inclusion_norm]
  exact (div_lt_iff₀ hbn).mpr (herr.trans_lt hn)

/-- Closedness of the already complete PreTilt image turns approximation into exact membership. -/
theorem norm_le_one_mem_range (x : InitialThetaTiltField.Carrier D w) (hx : ‖x‖ ≤ 1) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    x ∈ Set.range (InitialThetaTiltField.inclusion D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  obtain ⟨a, b, hb, rfl⟩ := fraction_representation D w x
  have hb' : InitialThetaTiltField.inclusion D w b ≠ 0 := by
    intro h
    exact hb ((InitialThetaTiltField.inclusion_injective D w) (h.trans (map_zero _).symm))
  have hab : ‖a‖ ≤ ‖b‖ := by
    rw [norm_div, InitialThetaPreTiltCompleteness.inclusion_norm,
      InitialThetaPreTiltCompleteness.inclusion_norm] at hx
    have hbn : 0 < ‖b‖ := by
      rw [← InitialThetaPreTiltCompleteness.inclusion_norm]
      exact norm_pos_iff.mpr hb'
    exact (div_le_one₀ hbn).mp hx
  exact (InitialThetaPreTiltCompleteness.inclusion_range_isClosed D w).closure_eq ▸
    integral_fraction_mem_closure D w a b hb hab

theorem inclusion_range_eq_closedBall :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    Set.range (InitialThetaTiltField.inclusion D w) = Metric.closedBall 0 1 := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  ext x
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨a, rfl⟩
    rw [InitialThetaPreTiltCompleteness.inclusion_norm]
    exact source_norm_le_one D w a
  · exact norm_le_one_mem_range D w x

theorem closedBall_isComplete :
    IsComplete (Metric.closedBall (0 : InitialThetaTiltField.Carrier D w) 1) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [← inclusion_range_eq_closedBall]
  exact InitialThetaPreTiltCompleteness.inclusion_range_isComplete D w

/-- Completeness is proved on the original tilt field, with its existing norm topology. -/
instance carrierCompleteSpace : CompleteSpace (InitialThetaTiltField.Carrier D w) :=
  NormedField.completeSpace_iff_isComplete_closedBall.mpr (closedBall_isComplete D w)

theorem cauchySeq_converges (s : ℕ → InitialThetaTiltField.Carrier D w) (hs : CauchySeq s) :
    ∃ x : InitialThetaTiltField.Carrier D w, Tendsto s atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hs

/-- A bounded-norm fraction is exactly an integral PreTilt element under inclusion. -/
theorem mem_inclusion_range_iff (x : InitialThetaTiltField.Carrier D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    x ∈ Set.range (InitialThetaTiltField.inclusion D w) ↔ ‖x‖ ≤ 1 := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [inclusion_range_eq_closedBall, Metric.mem_closedBall, dist_zero_right]

end
end JoshiTeich.Act1Scene1.InitialThetaTiltCompleteness
