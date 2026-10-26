import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
source-id: JT-SCENE1-WITT-COEFFICIENT-CONVERGENCE
source: Joshi II `se:ff-rings`, integral Witt coordinates and their
actual integral structure polynomials.
fidelity: coefficientwise convergence of original Witt vectors implies
convergence of every coefficient of their difference to zero. Evaluates
the actual Witt subtraction polynomial over the original topological ring.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this does not assume or assert convergence
in a rho norm. Uniform tail estimates are separate consumers.
-/

namespace JoshiTeich.Act1Scene1.WittCoefficientConvergence

open scoped Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]

theorem eval_sub_polynomial (a b : WittVector p F) (i : ℕ) :
    MvPolynomial.eval (Function.uncurry ![a.coeff, b.coeff])
        (MvPolynomial.map (Int.castRingHom F) (WittVector.wittSub p i)) = (a - b).coeff i := by
  rw [MvPolynomial.eval_map, WittVector.sub_coeff, WittVector.peval, MvPolynomial.aeval_def]
  rfl

theorem tendsto_sub_coeff (a : ℕ → WittVector p F) (b : WittVector p F)
    (ha : ∀ j : ℕ, Filter.Tendsto (fun m => (a m).coeff j) Filter.atTop (𝓝 (b.coeff j))) (i : ℕ) :
    Filter.Tendsto (fun m => (a m - b).coeff i) Filter.atTop (𝓝 0) := by
  have hx : Filter.Tendsto (fun m => Function.uncurry ![(a m).coeff, b.coeff]) Filter.atTop
      (𝓝 (Function.uncurry ![b.coeff, b.coeff])) := by
    apply tendsto_pi_nhds.mpr
    rintro ⟨j, n⟩
    fin_cases j
    · exact ha n
    · exact tendsto_const_nhds
  have h := (MvPolynomial.continuous_eval
    (MvPolynomial.map (Int.castRingHom F) (WittVector.wittSub p i))).continuousAt.tendsto.comp hx
  simpa only [Function.comp_def, eval_sub_polynomial, sub_self, WittVector.zero_coeff] using h

end
end JoshiTeich.Act1Scene1.WittCoefficientConvergence
