import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricPreTiltDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Valuation.Integral

/-!
source-id: JT-SCENE1-GEOMETRIC-PRETILT-POLYNOMIAL-ROOTS
source: Joshi tilt algebraic closedness after lem:perfectoid; actual coefficient
reduction, monic polynomial lifts and algebraically closed untilt roots.
fidelity: constructs bounded approximate roots of every nonconstant monic
polynomial over the original PreTilt, with an error vanishing at any specified
coefficient. No polynomial root or approximation certificate is input.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricPreTiltPolynomialRoots

open JoshiTeich.Prologue Polynomial
open scoped NNReal
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω] [CompleteSpace Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

/-- A prescribed coefficient of the evaluation vanishes at a bounded actual lift. -/
theorem exists_coeff_root (P : Polynomial (GeometricTiltField.Source Ω p))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) (n : ℕ) :
    ∃ x : GeometricTiltField.Source Ω p, ‖x‖ ≤ 1 ∧ PreTilt.coeff n (P.eval x) = 0 := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
  let Q := P.map (PreTilt.coeff n)
  have hQ : Q.Monic := hP.map _
  obtain ⟨R, hR, hRdeg, hRmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := q) Ideal.Quotient.mk_surjective Q) hQ
  have hmap : (R.map (algebraMap (LocalGeometricFontaine.integerRing Ω) Ω)).Monic := hRmon.map _
  have hmapdeg : (R.map (algebraMap (LocalGeometricFontaine.integerRing Ω) Ω)).natDegree ≠ 0 := by
    rw [hRmon.natDegree_map, hRdeg, hP.natDegree_map]
    exact hdeg
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (R.map (algebraMap (LocalGeometricFontaine.integerRing Ω) Ω))
    (Polynomial.degree_ne_of_natDegree_ne hmapdeg)
  have hir : IsIntegral (LocalGeometricFontaine.integerRing Ω) r :=
    ⟨R, hRmon, by simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hr⟩
  let z : LocalGeometricFontaine.integerRing Ω :=
    ⟨r, (Valuation.integer.integers (NormedField.valuation (K := Ω))).mem_of_integral hir⟩
  have hRz : R.eval z = 0 := by
    apply Subtype.ext
    change (algebraMap (LocalGeometricFontaine.integerRing Ω) Ω) (R.eval z) = 0
    rw [← Polynomial.eval_map_apply]
    exact hr
  let x := (frobenius (GeometricTiltField.Source Ω p) p)^[n] (GeometricTiltSharp.rootLift Ω p z)
  have hc : PreTilt.coeff n x = q z := by
    have hh := PreTilt.coeff_iterate_frobenius 0 n (GeometricTiltSharp.rootLift Ω p z)
    rw [Nat.zero_add] at hh
    change PreTilt.coeff n x = _ at hh
    rw [hh, ← PreTilt.mk_untilt_eq_coeff_zero, GeometricTiltSharp.untilt_rootLift]
  refine ⟨x, ?_, ?_⟩
  · rw [GeometricPreTiltCompleteness.norm_eq_valuation, GeometricTiltSharp.sourceValuation_eq_sharp_norm]
    change ‖(PreTilt.untilt x : LocalGeometricFontaine.integerRing Ω)‖ ≤ 1
    exact (LocalGeometricFontaine.mem_integerRing Ω _).mp (PreTilt.untilt x).property
  · rw [← Polynomial.eval_map_apply, hc]
    change Q.eval (q z) = 0
    rw [← hR, Polynomial.eval_map_apply, hRz, map_zero]

theorem exists_approx_root (P : Polynomial (GeometricTiltField.Source Ω p))
    (hP : P.Monic) (hdeg : P.natDegree ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : GeometricTiltField.Source Ω p, ‖x‖ ≤ 1 ∧ ‖P.eval x‖ < ε := by
  obtain ⟨n, hn⟩ := GeometricPreTiltCompleteness.exists_coeffRadius_lt Ω p ε hε
  obtain ⟨x, hx, he⟩ := exists_coeff_root Ω p P hP hdeg n
  exact ⟨x, hx, ((GeometricPreTiltCompleteness.coeff_eq_zero_iff Ω p (P.eval x) n).mp he).trans_lt hn⟩

end
end JoshiTeich.Act1Scene1.GeometricPreTiltPolynomialRoots
