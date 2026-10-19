import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltPolynomialRoots
import ArithmeticTeichmullerSpaces.Act1Scene1.CompleteFieldApproximateRoots
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltCompleteness
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-ALGEBRAICALLY-CLOSED
source: Joshi Arithmetic Holomorphic Structures tilt after lem:perfectoid;
actual integral coefficient roots, scaling and complete-field root criterion.
fidelity: proves algebraic closedness on the same actual complete normed tilt.
No algebraic closure replaces the carrier and no root/closedness certificate
is input. A selected paper tilt identity and holomorphoid marking remain open.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltAlgebraicallyClosed

open JoshiTeich.Prologue Polynomial
open scoped NNReal
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

/-- Approximate roots come from the actual integral PreTilt coefficients. -/
theorem integral_monic_approx_root (P : Polynomial (InitialThetaTiltField.Carrier D w))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) (hcoeff : ∀ i, ‖P.coeff i‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ x : InitialThetaTiltField.Carrier D w, ‖P.eval x‖ < ε := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  have hl : P ∈ Polynomial.lifts (InitialThetaTiltField.inclusion D w) := by
    apply (Polynomial.lifts_iff_coeff_lifts P).mpr
    intro i
    exact InitialThetaTiltCompleteness.norm_le_one_mem_range D w (P.coeff i) (hcoeff i)
  obtain ⟨R, hR, hRdeg, hRmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
  have hdegR : R.natDegree ≠ 0 := by rwa [hRdeg]
  obtain ⟨x, _, hx⟩ := GeometricPreTiltPolynomialRoots.exists_approx_root
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) (Arithmetic.residueChar w.1)
    R hRmon hdegR ε hε
  refine ⟨InitialThetaTiltField.inclusion D w x, ?_⟩
  rw [← hR, Polynomial.eval_map_apply, InitialThetaPreTiltCompleteness.inclusion_norm]
  exact hx

theorem integral_monic_root (P : Polynomial (InitialThetaTiltField.Carrier D w))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) (hcoeff : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ∃ x : InitialThetaTiltField.Carrier D w, P.eval x = 0 :=
  CompleteFieldApproximateRoots.exists_root P hP
    (integral_monic_approx_root D w P hP hdeg hcoeff)

/-- A nonzero contraction scales every nonleading coefficient of a given monic polynomial into O. -/
theorem exists_integral_scale (P : Polynomial (InitialThetaTiltField.Carrier D w)) (hP : P.Monic) :
    ∃ c : InitialThetaTiltField.Carrier D w, c ≠ 0 ∧ ∀ i, ‖(P.scaleRoots c).coeff i‖ ≤ 1 := by
  obtain ⟨t, ht0, ht1⟩ := InitialThetaTiltSharp.exists_contracting D w
  have htpos : 0 < ‖t‖ := by exact_mod_cast ht0
  have htlt : ‖t‖ < 1 := by exact_mod_cast ht1
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

/-- Scaling returns a genuine root of the original monic polynomial in the same tilt. -/
theorem monic_root (P : Polynomial (InitialThetaTiltField.Carrier D w))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) : ∃ x : InitialThetaTiltField.Carrier D w, P.eval x = 0 := by
  obtain ⟨c, hc0, hc⟩ := exists_integral_scale D w P hP
  obtain ⟨y, hy⟩ := integral_monic_root D w (P.scaleRoots c)
    ((Polynomial.monic_scaleRoots_iff c).mpr hP)
    (by rwa [Polynomial.natDegree_scaleRoots]) hc
  refine ⟨y / c, ?_⟩
  have he := Polynomial.scaleRoots_eval_mul P (y / c) c
  rw [mul_div_cancel₀ _ hc0, hy] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hc0)

instance carrierIsAlgClosed : IsAlgClosed (InitialThetaTiltField.Carrier D w) :=
  IsAlgClosed.of_exists_root _ fun P hP hi => monic_root D w P hP (Irreducible.natDegree_pos hi).ne'

/-- The full original tilt now has roots of every positive-order power. -/
theorem exists_pow_eq (x : InitialThetaTiltField.Carrier D w) (n : ℕ) (hn : 0 < n) :
    ∃ y : InitialThetaTiltField.Carrier D w, y ^ n = x := IsAlgClosed.exists_pow_nat_eq x hn

end
end JoshiTeich.Act1Scene1.InitialThetaTiltAlgebraicallyClosed
