import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithmInjective
import Mathlib.Topology.Order.LiminfLimsup

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-LOGARITHM-BOUNDED
source: Joshi II `eq:tate-module-of-lubin-tate`, `pr:teichmuller-lift-A/B`
and the rho norms on logarithmic Tate periods.
fidelity: bounds all actual Tate coordinates by one radius-dependent
constant strictly below one, using the proved Fontaine-kernel estimate.
Polynomial coefficient bounds and geometric decay give a common finite
bound for every Tate logarithm at that same radius.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; paper B identity and period/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithmBounded

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittTateLogarithm
open InitialThetaWittLogarithmSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_uniform_coordinate_bound (ρ : Radius) : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
    ∀ t : Tate D w, ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (coordinate D w t)‖ ≤ r := by
  refine ⟨max ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖
    ρ.val.toReal, (norm_nonneg _).trans (le_max_left _ _), ?_, ?_⟩
  · apply max_lt
    · exact (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2
    · simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
          ρ.property.2
  · intro t
    exact norm_ainf_kernel_le D w ρ _ (InitialThetaCyclotomicTateTilt.kernelCoordinate_mem_ker D w t)

theorem exists_uniform_tateLog_bound (ρ : Radius) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : Tate D w, ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (tateLog D w t)‖ ≤ C := by
  obtain ⟨r, hr, hr1, ht⟩ := exists_uniform_coordinate_bound D w ρ
  obtain ⟨k, hk⟩ := InitialThetaWittLogDenominatorBounds.exists_polynomial_bound D w ρ
  obtain ⟨C, hC⟩ := (tendsto_pow_const_mul_const_pow_of_lt_one k hr hr1).bddAbove_range
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  have hs := (InitialThetaWittAllRadiusSeries.hasSum_iff_coordinates D w _ _).mp
    (hasSum_tateLog D w t) ρ
  rw [← hs.tsum_eq]
  apply UltrametricLogTailBounds.norm_tsum_le_of_forall_le _ hs.summable _ (le_max_right _ _)
  intro n
  apply (norm_evaluate_logTerm_le D w ρ k hk (coordinate D w t) n).trans
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (ht t) n) (pow_nonneg (Nat.cast_nonneg n) k)).trans
      ((hC (Set.mem_range_self n)).trans (le_max_left _ _))

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateLogarithmBounded
