import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltPolynomialRoots
import ArithmeticTeichmullerSpaces.Act1Scene1.CompleteFieldApproximateRoots
import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltCompleteness
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
source-id: JT-SCENE1-GEOMETRIC-TILT-ALGEBRAICALLY-CLOSED
source: Joshi Arithmetic Holomorphic Structures tilt after lem:perfectoid;
the original local integral approximate-root, scaling and complete-field
root construction, now for every complete algebraically closed untilt.
fidelity: proves algebraic closedness on the original PreTilt fraction
field, with its original valuation norm. No algebraic closure replaces the
carrier, and no root or algebraic-closedness certificate for this fraction
field is input. Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricTiltAlgebraicallyClosed

open JoshiTeich.Prologue Polynomial
open scoped NNReal
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω] [CompleteSpace Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

local instance fractionNormedField : NormedField (GeometricTiltField.FractionField Ω p) :=
  GeometricTiltNorm.fractionNormedField Ω p

local instance fractionUltrametric : IsUltrametricDist (GeometricTiltField.FractionField Ω p) :=
  GeometricTiltNorm.fractionUltrametric Ω p

local instance fractionCompleteSpace : CompleteSpace (GeometricTiltField.FractionField Ω p) :=
  GeometricTiltCompleteness.fractionCompleteSpace Ω p

/-- The sharp preimage of the untilt prime is a nonzero contraction. -/
theorem exists_contracting : ∃ t : GeometricTiltField.FractionField Ω p, 0 < ‖t‖ ∧ ‖t‖ < 1 := by
  obtain ⟨t, ht⟩ := GeometricTiltSharp.sharp_surjective Ω p (p : Ω)
  have hnorm : ‖t‖ = ‖(p : Ω)‖ := by
    calc
      ‖t‖ = (GeometricTiltField.fractionValuation Ω p t : ℝ) :=
        GeometricTiltNorm.norm_eq_valuation Ω p t
      _ = ‖GeometricTiltSharp.sharp Ω p t‖ :=
        congrArg (fun r : ℝ≥0 => (r : ℝ)) (GeometricTiltSharp.sharp_norm Ω p t).symm
      _ = ‖(p : Ω)‖ := congrArg norm ht
  exact ⟨t, hnorm.symm ▸ hp.out.1, hnorm.symm ▸ hp.out.2⟩

local instance fractionNontriviallyNormedField :
    NontriviallyNormedField (GeometricTiltField.FractionField Ω p) where
  toNormedField := GeometricTiltNorm.fractionNormedField Ω p
  non_trivial := by
    obtain ⟨t, ht0, ht1⟩ := exists_contracting Ω p
    refine ⟨t⁻¹, ?_⟩
    rw [norm_inv]
    exact (one_lt_inv₀ ht0).mpr ht1

/-- Approximate roots come from the actual integral PreTilt coefficients. -/
theorem integral_monic_approx_root (P : Polynomial (GeometricTiltField.FractionField Ω p))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) (hcoeff : ∀ i, ‖P.coeff i‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ x : GeometricTiltField.FractionField Ω p, ‖P.eval x‖ < ε := by
  have hl : P ∈ Polynomial.lifts
      (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p)) := by
    apply (Polynomial.lifts_iff_coeff_lifts P).mpr
    intro i
    exact GeometricTiltCompleteness.norm_le_one_mem_range Ω p (P.coeff i) (hcoeff i)
  obtain ⟨R, hR, hRdeg, hRmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
  have hdegR : R.natDegree ≠ 0 := by rwa [hRdeg]
  obtain ⟨x, _, hx⟩ := GeometricPreTiltPolynomialRoots.exists_approx_root Ω p R hRmon hdegR ε hε
  refine ⟨algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) x, ?_⟩
  rw [← hR, Polynomial.eval_map_apply, GeometricTiltNorm.inclusion_norm]
  exact hx

theorem integral_monic_root (P : Polynomial (GeometricTiltField.FractionField Ω p))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) (hcoeff : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ∃ x : GeometricTiltField.FractionField Ω p, P.eval x = 0 :=
  CompleteFieldApproximateRoots.exists_root P hP
    (integral_monic_approx_root Ω p P hP hdeg hcoeff)

/-- A nonzero contraction scales all coefficients of a monic polynomial into the unit ball. -/
theorem exists_integral_scale (P : Polynomial (GeometricTiltField.FractionField Ω p)) (hP : P.Monic) :
    ∃ c : GeometricTiltField.FractionField Ω p,
      c ≠ 0 ∧ ∀ i, ‖(P.scaleRoots c).coeff i‖ ≤ 1 := by
  obtain ⟨t, htpos, htlt⟩ := exists_contracting Ω p
  let M := max P.supNorm 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hM) htlt
  let c := t ^ n
  have hc0 : c ≠ 0 := pow_ne_zero n (norm_pos_iff.mp htpos)
  have hcn : ‖c‖ < 1 / M := by simpa only [c, norm_pow] using hn
  have hc1 : ‖c‖ ≤ 1 := hcn.le.trans ((div_le_one₀ hM).mpr (le_max_right _ _))
  refine ⟨c, hc0, ?_⟩
  intro i
  by_cases hi : i < P.natDegree
  · rw [Polynomial.coeff_scaleRoots, norm_mul, norm_pow]
    have hpw : ‖c‖ ^ (P.natDegree - i) ≤ ‖c‖ :=
      pow_le_of_le_one (norm_nonneg _) hc1 (Nat.sub_ne_zero_of_lt hi)
    have hm : ‖P.coeff i‖ ≤ M := (P.le_supNorm i).trans (le_max_left _ _)
    have hmul : M * ‖c‖ < 1 := by
      have hh := (lt_div_iff₀ hM).mp hcn
      simpa only [mul_comm] using hh
    exact (mul_le_mul hm hpw (pow_nonneg (norm_nonneg _) _) hM.le).trans hmul.le
  · by_cases he : i = P.natDegree
    · subst i
      rw [Polynomial.coeff_scaleRoots_natDegree, hP.leadingCoeff, norm_one]
    · have hz : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp only [Polynomial.coeff_scaleRoots, hz, zero_mul, norm_zero, zero_le_one]

/-- Scaling returns a root of the original monic polynomial in the same fraction field. -/
theorem monic_root (P : Polynomial (GeometricTiltField.FractionField Ω p))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) :
    ∃ x : GeometricTiltField.FractionField Ω p, P.eval x = 0 := by
  obtain ⟨c, hc0, hc⟩ := exists_integral_scale Ω p P hP
  obtain ⟨y, hy⟩ := integral_monic_root Ω p (P.scaleRoots c)
    ((Polynomial.monic_scaleRoots_iff c).mpr hP)
    (by rwa [Polynomial.natDegree_scaleRoots]) hc
  refine ⟨y / c, ?_⟩
  have he := Polynomial.scaleRoots_eval_mul P (y / c) c
  rw [mul_div_cancel₀ _ hc0, hy] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hc0)

/-- Algebraic closedness is a proved structure for local use on the original carrier. -/
theorem fractionIsAlgClosed : IsAlgClosed (GeometricTiltField.FractionField Ω p) :=
  IsAlgClosed.of_exists_root _ fun P hP hi =>
    monic_root Ω p P hP (Irreducible.natDegree_pos hi).ne'

/-- Every element of the same fraction field has roots of every positive order. -/
theorem exists_pow_eq (x : GeometricTiltField.FractionField Ω p) (n : ℕ) (hn : 0 < n) :
    ∃ y : GeometricTiltField.FractionField Ω p, y ^ n = x := by
  letI := fractionIsAlgClosed Ω p
  exact IsAlgClosed.exists_pow_nat_eq x hn

end
end JoshiTeich.Act1Scene1.GeometricTiltAlgebraicallyClosed
