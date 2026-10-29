import ArithmeticTeichmullerSpaces.Act1Scene1.WittIntegralCoefficientBounds

/-!
source-id: JT-SCENE1-WITT-LOCAL-COEFFICIENT-BOUNDS
source: Joshi II `se:ff-rings`, the original integral Witt structure
polynomials used to recover coefficients from rho-Cauchy approximants.
fidelity: localizes the integral coefficient estimates to the actual
finite support of the nth Witt polynomial. Only the first n+1 input
coefficients need be integral. Original proofs; no reference code copied.
boundary: Scene1/Derived; radius bounds and completed coefficient
recovery are supplied by actual source consumers. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.WittLocalCoefficientBounds

open UltrametricIntegralPolynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [NormedCommRing F] [NormOneClass F] [IsUltrametricDist F]

theorem norm_sub_coeff_le_one_of_head (a b : WittVector p F) (n : ℕ)
    (ha : ∀ i ≤ n, ‖a.coeff i‖ ≤ 1) (hb : ∀ i ≤ n, ‖b.coeff i‖ ≤ 1) :
    ‖(a - b).coeff n‖ ≤ 1 := by
  classical
  let x : Fin 2 × ℕ → F := fun i =>
    if i.2 ≤ n then Function.uncurry ![a.coeff, b.coeff] i else 0
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro ⟨i, j⟩
    dsimp only [x]
    split_ifs with hj
    · fin_cases i
      · exact ha j hj
      · exact hb j hj
    · simpa only [norm_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
  have he : MvPolynomial.eval₂Hom (Int.castRingHom F) x (WittVector.wittSub p n) =
      (a - b).coeff n := by
    calc
      _ = MvPolynomial.eval₂Hom (Int.castRingHom F)
          (Function.uncurry ![a.coeff, b.coeff]) (WittVector.wittSub p n) := by
        apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
        rintro ⟨i, j⟩ hij _
        exact ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp
          (Finset.mem_product.mp (WittVector.wittSub_vars p n hij)).2))
      _ = _ := by rw [WittVector.sub_coeff, WittVector.peval, MvPolynomial.aeval_def]; rfl
  rw [← he]
  exact norm_eval_le_one _ x hx

theorem norm_coeff_sub_le_of_head (a b : WittVector p F) (n : ℕ)
    (hb : ∀ i ≤ n, ‖b.coeff i‖ ≤ 1) (hd : ∀ i ≤ n, ‖(a - b).coeff i‖ ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ i ≤ n, ‖(a - b).coeff i‖ ≤ B) :
    ‖a.coeff n - b.coeff n‖ ≤ B := by
  classical
  let x : Fin 2 × ℕ → F := fun i =>
    if i.2 ≤ n then Function.uncurry ![(a - b).coeff, b.coeff] i else 0
  let y : Fin 2 × ℕ → F := fun i =>
    if i.2 ≤ n then Function.uncurry ![(0 : WittVector p F).coeff, b.coeff] i else 0
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro ⟨i, j⟩
    dsimp only [x]
    split_ifs with hj
    · fin_cases i
      · exact hd j hj
      · exact hb j hj
    · simpa only [norm_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
  have hy : ∀ i, ‖y i‖ ≤ 1 := by
    rintro ⟨i, j⟩
    dsimp only [y]
    split_ifs with hj
    · fin_cases i
      · change ‖(0 : WittVector p F).coeff j‖ ≤ 1
        rw [WittVector.zero_coeff, norm_zero]
        exact zero_le_one
      · exact hb j hj
    · simpa only [norm_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
  have hxy : ∀ i, ‖x i - y i‖ ≤ B := by
    rintro ⟨i, j⟩
    dsimp only [x, y]
    split_ifs with hj
    · fin_cases i
      · change ‖(a - b).coeff j - (0 : WittVector p F).coeff j‖ ≤ B
        simpa only [WittVector.zero_coeff, sub_zero] using h j hj
      · change ‖b.coeff j - b.coeff j‖ ≤ B
        simpa only [sub_self, norm_zero] using hB
    · simpa only [sub_self, norm_zero] using hB
  have he (u v : WittVector p F) :
      MvPolynomial.eval₂Hom (Int.castRingHom F)
        (fun i : Fin 2 × ℕ => if i.2 ≤ n then Function.uncurry ![u.coeff, v.coeff] i else 0)
        (WittVector.wittAdd p n) = (u + v).coeff n := by
    calc
      _ = MvPolynomial.eval₂Hom (Int.castRingHom F)
          (Function.uncurry ![u.coeff, v.coeff]) (WittVector.wittAdd p n) := by
        apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
        rintro ⟨i, j⟩ hij _
        exact ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp
          (Finset.mem_product.mp (WittVector.wittAdd_vars p n hij)).2))
      _ = _ := by rw [WittVector.add_coeff, WittVector.peval, MvPolynomial.aeval_def]; rfl
  have hbound := norm_eval_sub_le (WittVector.wittAdd p n) x y hx hy B hB hxy
  simpa only [x, y, he, sub_add_cancel, zero_add] using hbound

end
end JoshiTeich.Act1Scene1.WittLocalCoefficientBounds
