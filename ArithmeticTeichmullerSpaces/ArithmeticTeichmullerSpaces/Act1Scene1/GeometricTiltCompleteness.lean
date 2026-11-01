import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltDivision

/-!
source-id: JT-SCENE1-GEOMETRIC-TILT-COMPLETENESS
source: Joshi Arithmetic Holomorphic Structures tilt after lem:perfectoid;
the locally proved PreTilt coefficient limits and division approximations.
fidelity: generalizes the existing actual tilt completeness proof to a complete
algebraically closed coefficient field. The original PreTilt image is the
closed unit ball, and the original fraction field is complete with its valuation
norm. No completion replaces its carrier and no completeness certificate is input.
Original local proofs; no reference source code copied.
boundary: Scene1/Derived; paper period-ring identities remain separate. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricTiltCompleteness

open JoshiTeich.Prologue
open GeometricTiltField
open scoped NNReal Topology
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω] [CompleteSpace Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]
variable [IsAlgClosed Ω]

local instance normedFractionField : NormedField (FractionField Ω p) :=
  GeometricTiltNorm.fractionNormedField Ω p

local notation "ι" => algebraMap (Source Ω p) (FractionField Ω p)

/-- Fractions represent elements of the original tilt carrier. -/
theorem fraction_representation (x : FractionField Ω p) :
    ∃ a b : Source Ω p, b ≠ 0 ∧ ι a / ι b = x := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (Source Ω p) x
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, hx⟩

theorem source_norm_le_one (a : Source Ω p) : ‖a‖ ≤ 1 := by
  have h := GeometricPreTiltDivision.shiftedUntilt_norm_pow Ω p a 0
  simp only [pow_zero, pow_one] at h
  rw [← h]
  exact (LocalGeometricFontaine.mem_integerRing Ω _).mp
    (GeometricPreTiltDivision.shiftedUntilt Ω p a 0).property

/-- Integral fractions admit arbitrary-precision approximations in the original PreTilt. -/
theorem integral_fraction_mem_closure (a b : Source Ω p) (hb : b ≠ 0)
    (hab : ‖a‖ ≤ ‖b‖) :
    ι a / ι b ∈ closure (Set.range ι) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hb' : ι b ≠ 0 := by
    intro h
    exact hb ((IsFractionRing.injective (Source Ω p) (FractionField Ω p))
      (h.trans (map_zero _).symm))
  have hbn : 0 < ‖ι b‖ := norm_pos_iff.mpr hb'
  obtain ⟨n, hn⟩ := GeometricPreTiltCompleteness.exists_coeffRadius_lt Ω p
    (ε * ‖ι b‖) (mul_pos hε hbn)
  let c := GeometricPreTiltDivision.approximation Ω p a b hb hab n
  refine ⟨ι c, ⟨c, rfl⟩, ?_⟩
  have herr := GeometricPreTiltDivision.approximation_error_norm Ω p a b hb hab n
  have heq : ι a / ι b - ι c = ι (a - b * c) / ι b := by
    rw [map_sub, map_mul]
    field_simp
  rw [dist_eq_norm, heq, norm_div, GeometricTiltNorm.inclusion_norm]
  exact (div_lt_iff₀ hbn).mpr (herr.trans_lt hn)

/-- Closedness turns the actual division approximations into exact PreTilt membership. -/
theorem norm_le_one_mem_range (x : FractionField Ω p) (hx : ‖x‖ ≤ 1) :
    x ∈ Set.range ι := by
  obtain ⟨a, b, hb, rfl⟩ := fraction_representation Ω p x
  have hb' : ι b ≠ 0 := by
    intro h
    exact hb ((IsFractionRing.injective (Source Ω p) (FractionField Ω p))
      (h.trans (map_zero _).symm))
  have hab : ‖a‖ ≤ ‖b‖ := by
    rw [norm_div, GeometricTiltNorm.inclusion_norm,
      GeometricTiltNorm.inclusion_norm] at hx
    have hbn : 0 < ‖b‖ := by
      rw [← GeometricTiltNorm.inclusion_norm Ω p b]
      exact norm_pos_iff.mpr hb'
    exact (div_le_one₀ hbn).mp hx
  exact (GeometricTiltNorm.inclusion_range_isClosed Ω p).closure_eq ▸
    integral_fraction_mem_closure Ω p a b hb hab

theorem inclusion_range_eq_closedBall :
    Set.range ι = Metric.closedBall 0 1 := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨a, rfl⟩
    rw [GeometricTiltNorm.inclusion_norm]
    exact source_norm_le_one Ω p a
  · exact norm_le_one_mem_range Ω p x

theorem closedBall_isComplete :
    IsComplete (Metric.closedBall (0 : FractionField Ω p) 1) := by
  rw [← inclusion_range_eq_closedBall Ω p]
  exact GeometricTiltNorm.inclusion_range_isComplete Ω p

/-- Completeness uses the valuation norm on the original fraction field. -/
theorem fractionCompleteSpace :
    letI := GeometricTiltNorm.fractionNormedField Ω p
    CompleteSpace (FractionField Ω p) :=
  NormedField.completeSpace_iff_isComplete_closedBall.mpr (closedBall_isComplete Ω p)

end
end JoshiTeich.Act1Scene1.GeometricTiltCompleteness
