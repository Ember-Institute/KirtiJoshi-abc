import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Algebra.MvPolynomial.Variables

/-!
source-id: JT-SCENE1-ULTRAMETRIC-INTEGRAL-POLYNOMIAL
source: Joshi II `se:ff-rings`, continuity of original Witt coordinates;
integer Witt structure polynomials on an ultrametric unit ball.
fidelity: proves that every integral multivariate polynomial preserves
the norm unit ball and is nonexpanding there. The difference bound can
be supplied only on the polynomial's actual finite variable support.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no Witt coordinate continuity or completeness
is assumed. Actual coefficient bounds are separate consumers.
-/

namespace JoshiTeich.Act1Scene1.UltrametricIntegralPolynomial

noncomputable section
variable {F : Type*} [NormedCommRing F] [NormOneClass F] [IsUltrametricDist F]
variable {σ : Type*}

theorem norm_eval_le_one (P : MvPolynomial σ ℤ) (x : σ → F) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ‖MvPolynomial.eval₂Hom (Int.castRingHom F) x P‖ ≤ 1 := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.eval₂Hom_C]
    exact IsUltrametricDist.norm_intCast_le_one F c
  | add P Q hP hQ =>
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hP hQ)
  | mul_X P i hP =>
    rw [map_mul, MvPolynomial.eval₂Hom_X']
    exact (norm_mul_le _ _).trans (mul_le_one₀ hP (norm_nonneg _) (hx i))

theorem norm_eval_sub_le (P : MvPolynomial σ ℤ) (x y : σ → F)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (hxy : ∀ i, ‖x i - y i‖ ≤ B) :
    ‖MvPolynomial.eval₂Hom (Int.castRingHom F) x P -
      MvPolynomial.eval₂Hom (Int.castRingHom F) y P‖ ≤ B := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂Hom_C, sub_self, norm_zero] using hB
  | add P Q hP hQ =>
    rw [map_add, map_add, add_sub_add_comm]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hP hQ)
  | mul_X P i hP =>
    rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
    have he : MvPolynomial.eval₂Hom (Int.castRingHom F) x P * x i -
        MvPolynomial.eval₂Hom (Int.castRingHom F) y P * y i =
      MvPolynomial.eval₂Hom (Int.castRingHom F) x P * (x i - y i) +
        (MvPolynomial.eval₂Hom (Int.castRingHom F) x P -
          MvPolynomial.eval₂Hom (Int.castRingHom F) y P) * y i := by ring
    rw [he]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (norm_eval_le_one P x hx)).trans (hxy i))
    · exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (hy i)).trans hP)

theorem norm_eval_sub_le_of_vars (P : MvPolynomial σ ℤ) (x y : σ → F)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (hxy : ∀ i ∈ P.vars, ‖x i - y i‖ ≤ B) :
    ‖MvPolynomial.eval₂Hom (Int.castRingHom F) x P -
      MvPolynomial.eval₂Hom (Int.castRingHom F) y P‖ ≤ B := by
  classical
  let x' : σ → F := fun i => if i ∈ P.vars then x i else 0
  let y' : σ → F := fun i => if i ∈ P.vars then y i else 0
  have he (f : σ → F) : MvPolynomial.eval₂Hom (Int.castRingHom F)
      (fun i => if i ∈ P.vars then f i else 0) P = MvPolynomial.eval₂Hom (Int.castRingHom F) f P :=
    MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => if_pos hi) rfl
  have hx' : ∀ i, ‖x' i‖ ≤ 1 := by intro i; dsimp only [x']; split_ifs <;> simp_all
  have hy' : ∀ i, ‖y' i‖ ≤ 1 := by intro i; dsimp only [y']; split_ifs <;> simp_all
  have hxy' : ∀ i, ‖x' i - y' i‖ ≤ B := by
    intro i
    dsimp only [x', y']
    split_ifs with hi
    · exact hxy i hi
    · simpa only [sub_self, norm_zero] using hB
  simpa only [x', y', he] using norm_eval_sub_le P x' y' hx' hy' B hB hxy'

end
end JoshiTeich.Act1Scene1.UltrametricIntegralPolynomial
