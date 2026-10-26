import ArithmeticTeichmullerSpaces.Act1Scene1.UltrametricIntegralPolynomial
import Mathlib.RingTheory.WittVector.Basic

/-!
source-id: JT-SCENE1-WITT-INTEGRAL-COEFFICIENT-BOUNDS
source: Joshi II `se:ff-rings`, the topology on the original integral
Witt source; the actual integral Witt addition polynomials.
fidelity: on Witt vectors whose coefficients and difference coefficients
have norm at most one, bounds the nth coefficient difference by any
common bound on the first n+1 coefficients of the Witt difference.
Uses the actual polynomial and its proved finite variable support.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; rho estimates and coefficient Cauchy limits
are supplied by the actual source consumer. No continuity is input.
-/

namespace JoshiTeich.Act1Scene1.WittIntegralCoefficientBounds

open UltrametricIntegralPolynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedCommRing F] [NormOneClass F] [IsUltrametricDist F]

theorem norm_coeff_sub_le (a b : WittVector p F)
    (hb : ∀ i, ‖b.coeff i‖ ≤ 1) (hd : ∀ i, ‖(a - b).coeff i‖ ≤ 1)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i ≤ n, ‖(a - b).coeff i‖ ≤ B) :
    ‖a.coeff n - b.coeff n‖ ≤ B := by
  let x : Fin 2 × ℕ → F := Function.uncurry ![(a - b).coeff, b.coeff]
  let y : Fin 2 × ℕ → F := Function.uncurry ![(0 : WittVector p F).coeff, b.coeff]
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro ⟨i, j⟩
    fin_cases i
    · exact hd j
    · exact hb j
  have hy : ∀ i, ‖y i‖ ≤ 1 := by
    rintro ⟨i, j⟩
    fin_cases i
    · change ‖(0 : WittVector p F).coeff j‖ ≤ 1
      rw [WittVector.zero_coeff, norm_zero]
      exact zero_le_one
    · exact hb j
  have hxy : ∀ i ∈ (WittVector.wittAdd p n).vars, ‖x i - y i‖ ≤ B := by
    rintro ⟨i, j⟩ hij
    have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp
      (Finset.mem_product.mp (WittVector.wittAdd_vars p n hij)).2)
    fin_cases i
    · change ‖(a - b).coeff j - (0 : WittVector p F).coeff j‖ ≤ B
      rw [WittVector.zero_coeff, sub_zero]
      exact h j hj
    · change ‖b.coeff j - b.coeff j‖ ≤ B
      simpa only [sub_self, norm_zero] using hB
  have hbound := norm_eval_sub_le_of_vars (WittVector.wittAdd p n) x y hx hy B hB hxy
  have he (u v : WittVector p F) :
      MvPolynomial.eval₂Hom (Int.castRingHom F) (Function.uncurry ![u.coeff, v.coeff])
        (WittVector.wittAdd p n) = (u + v).coeff n := by
    rw [WittVector.add_coeff, WittVector.peval, MvPolynomial.aeval_def]
    rfl
  simpa only [x, y, he, sub_add_cancel, zero_add] using hbound

end
end JoshiTeich.Act1Scene1.WittIntegralCoefficientBounds
