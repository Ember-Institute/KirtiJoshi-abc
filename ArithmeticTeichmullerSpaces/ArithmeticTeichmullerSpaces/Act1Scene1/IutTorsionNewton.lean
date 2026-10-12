/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Tripod/TorsionNewton.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `225164d1a47b377fac3bff58a22e43ec7f9cc676`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: extracts the integral-model Newton proof and uses local division
polynomials. New proofs complete the square, prove finite model exceptions,
and bound the translated sums for actual four-torsion point pairs.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutFourTorsionSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCyclicVeluRatio

/-!
source-id: IUT-COR312-TORSION-NEWTON-BOUND
fidelity: division-polynomial integrality and a dominant-term argument give
`|n|² |x(P)| ≤ 1` on an integral model with a₁ = a₃ = 0. Completing the square
preserves x and gives the same bound on any number-field curve away from a
proved finite set of coefficient places. Finite subgroup translations of
four-torsion point pairs give an actual additive sum bound at these places.
The Vélu additive identity, estimates at excluded and infinite places, and
height transport remain open. No Legendre model or Heights dependency is used.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutTorsionNewton

open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)

/-- The ultrametric inequality for finite sums: if every term has `|·|_w ≤ B` and `B ≥ 0`,
so does the sum. -/
lemma apply_sum_le {ι : Type*} (s : Finset ι) (f : ι → K) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, w (f i) ≤ B) : w (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (FinitePlace.add_le w _ _).trans (max_le (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The subring of `w`-integral elements. -/
def integers : Subring K where
  carrier := {z | w z ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
    exact mul_le_one₀ ha (apply_nonneg w b) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (FinitePlace.add_le w a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

lemma mem_integers {z : K} : z ∈ integers w ↔ w z ≤ 1 := Iff.rfl

/-- The integral model of `W` over the `w`-integral elements. -/
def intModel (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1) (h₃ : w W.a₃ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) : WeierstrassCurve (integers w) :=
  ⟨⟨W.a₁, h₁⟩, ⟨W.a₂, h₂⟩, ⟨W.a₃, h₃⟩, ⟨W.a₄, h₄⟩, ⟨W.a₆, h₆⟩⟩

lemma intModel_map (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1) (h₃ : w W.a₃ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) :
    (intModel w W h₁ h₂ h₃ h₄ h₆).map (integers w).subtype = W := rfl

/-- The coefficients of the division polynomials of an integral model are integral. -/
lemma apply_coeff_ΨSq_le_one (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1)
    (h₃ : w W.a₃ ≤ 1) (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) (n : ℤ) (k : ℕ) :
    w ((W.ΨSq n).coeff k) ≤ 1 := by
  rw [← intModel_map w W h₁ h₂ h₃ h₄ h₆, map_ΨSq, coeff_map]
  exact ((intModel w W h₁ h₂ h₃ h₄ h₆).ΨSq n).coeff k |>.2

/-- **The Newton bound for torsion points**: on a model with `a₁ = a₃ = 0` and `w`-integral
`a₂, a₄, a₆`, an affine point `(x, y)` with `n • (x, y) = 0` (`n ≥ 1`) has `|n|_w² |x|_w ≤ 1`. -/
theorem apply_x_le {W : Affine K} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (h₂ : w W.a₂ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) {n : ℕ} (hn : 1 ≤ n) {x y : K}
    (h : W.Nonsingular x y) (hP : n • Point.some x y h = 0) :
    w (n : K) ^ 2 * w x ≤ 1 := by
  have h₁ : w W.a₁ ≤ 1 := by rw [ha₁, map_zero]; exact zero_le_one
  have h₃ : w W.a₃ ≤ 1 := by rw [ha₃, map_zero]; exact zero_le_one
  have hroot : (W.ΨSq n).eval x = 0 := (JoshiTeich.ReferenceIut.Torsion.smul_eq_zero_iff_ΨSq ha₁ ha₃ h n).mp hP
  have hna : IsNonarchimedean w := fun a b => FinitePlace.add_le w a b
  have hn1 : (1 : ℝ) ≥ w (n : K) :=
    IsNonarchimedean.apply_natCast_le_one (f := w) (map_zero_le w 1) (map_one w) hna
  by_cases hx : w x ≤ 1
  · exact mul_le_one₀ (pow_le_one₀ (n := 2) (apply_nonneg w _) hn1) (apply_nonneg w x) hx
  rw [not_le] at hx
  set D := n ^ 2 - 1 with hD
  have hdeg : (W.ΨSq n).natDegree ≤ D := by
    have := natDegree_ΨSq_le W (n : ℤ)
    simpa [hD] using this
  have hlead : (W.ΨSq n).coeff D = (n : K) ^ 2 := by
    have := coeff_ΨSq W (n : ℤ)
    simpa [hD] using this
  have hsum := (W.ΨSq n).eval_eq_sum_range' (Nat.lt_succ_of_le hdeg) x
  rw [hroot, Finset.sum_range_succ, hlead] at hsum
  -- the leading term equals minus the sum of the lower terms
  have hlt : (n : K) ^ 2 * x ^ D = -∑ i ∈ Finset.range D, (W.ΨSq n).coeff i * x ^ i := by
    linear_combination -hsum
  have hbound : w (∑ i ∈ Finset.range D, (W.ΨSq n).coeff i * x ^ i) ≤ w x ^ (D - 1) := by
    refine apply_sum_le w _ _ (by positivity) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc w ((W.ΨSq n).coeff i) * w x ^ i ≤ 1 * w x ^ (D - 1) := by
          gcongr
          · exact apply_coeff_ΨSq_le_one w W h₁ h₂ h₃ h₄ h₆ n i
          · exact hx.le
          · omega
      _ = w x ^ (D - 1) := one_mul _
  have hD1 : 1 ≤ D := by
    by_contra hD0
    have hD0 : D = 0 := by omega
    rw [hD0, pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, neg_zero] at hlt
    have hn0 : (n : K) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact pow_ne_zero 2 hn0 hlt
  have hkey : w (n : K) ^ 2 * w x ^ D ≤ w x ^ (D - 1) := by
    have := congrArg w hlt
    rw [map_mul, map_pow, map_pow, map_neg_eq_map] at this
    rw [this]
    exact hbound
  have hxpos : 0 < w x := lt_trans zero_lt_one hx
  have : w x ^ D = w x ^ (D - 1) * w x := by
    rw [← pow_succ]; congr 1; omega
  rw [this, ← mul_assoc, mul_comm _ (w x ^ (D - 1)), mul_assoc] at hkey
  have hp : 0 < w x ^ (D - 1) := pow_pos hxpos _
  have := le_of_mul_le_mul_left (by linarith : w x ^ (D - 1) * (w (n : K) ^ 2 * w x) ≤
    w x ^ (D - 1) * 1) hp
  exact this

open IutCyclicVelu IutGeometricTorsion
open JoshiTeich.ReferenceIut.Anabelian

/-- Completing the square keeps the x coordinate in the Newton bound. -/
theorem apply_xCoordinate_le_completedSquare (W : WeierstrassCurve K)
    (h₂ : w (completeSquare W • W).a₂ ≤ 1)
    (h₄ : w (completeSquare W • W).a₄ ≤ 1)
    (h₆ : w (completeSquare W • W).a₆ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (P : W.toAffine.Point) (hP : n • P = 0) :
    w (n : K) ^ 2 * w (xCoordinate P) ≤ 1 := by
  cases P with
  | zero => simp [xCoordinate]
  | some x y h =>
    let C := completeSquare W
    have hP' : n • vcEquiv C W (Affine.Point.some x y h) = 0 := by
      rw [← map_nsmul, hP, map_zero]
    change n • Affine.Point.some (vcX C x) (vcY C x y) _ = 0 at hP'
    have hN := apply_x_le w (completeSquare_a₁ W) (completeSquare_a₃ W)
      h₂ h₄ h₆ hn _ hP'
    simpa [C, vcX, completeSquare, xCoordinate] using hN

/-- A fixed coefficient is nonintegral at only finitely many finite places. -/
lemma finite_nonintegral_places (a : K) : {v : FinitePlace K | 1 < v a}.Finite := by
  by_cases ha : a = 0
  · subst a
    have hz : {v : FinitePlace K | 1 < v (0 : K)} = ∅ := by
      ext v
      simp
    rw [hz]
    exact Set.finite_empty
  · exact (FinitePlace.hasFiniteMulSupport ha).subset fun v hv => ne_of_gt hv

/-- The finite places where a coefficient of the completed model is nonintegral. -/
def modelBadPlaces (W : WeierstrassCurve K) : Set (FinitePlace K) :=
  {v | 1 < v (completeSquare W • W).a₂ ∨
    1 < v (completeSquare W • W).a₄ ∨ 1 < v (completeSquare W • W).a₆}

lemma modelBadPlaces_finite (W : WeierstrassCurve K) : (modelBadPlaces W).Finite := by
  unfold modelBadPlaces
  simp only [Set.setOf_or]
  exact (finite_nonintegral_places (completeSquare W • W).a₂).union
    ((finite_nonintegral_places (completeSquare W • W).a₄).union
      (finite_nonintegral_places (completeSquare W • W).a₆))

/-- The Newton bound on any number-field curve outside the actual coefficient exceptions. -/
theorem apply_xCoordinate_le_of_notMem_modelBadPlaces (W : WeierstrassCurve K)
    (hw : w ∉ modelBadPlaces W) {n : ℕ} (hn : 1 ≤ n)
    (P : W.toAffine.Point) (hP : n • P = 0) :
    w (n : K) ^ 2 * w (xCoordinate P) ≤ 1 := by
  simp only [modelBadPlaces, Set.mem_setOf_eq, not_or] at hw
  exact apply_xCoordinate_le_completedSquare w W (not_lt.mp hw.1)
    (not_lt.mp hw.2.1) (not_lt.mp hw.2.2) hn P hP

variable {W : WeierstrassCurve K}

/-- The additive expression that occurs in the Vélu ratio identity. -/
noncomputable def translatedSum (H : AddSubgroup W.toAffine.Point) [Fintype H]
    (T R : W.toAffine.Point) : K :=
  (∑ Q : H, xCoordinate (T + (Q : W.toAffine.Point))) -
    ∑ Q : H, xCoordinate (R + (Q : W.toAffine.Point))

/-- Finite subgroup translations of four-torsion points satisfy the Newton sum bound. -/
theorem translatedSum_le (H : AddSubgroup W.toAffine.Point) [Fintype H]
    (hw : w ∉ modelBadPlaces W) (T R : W.toAffine.Point)
    (hT : 4 • T = 0) (hR : 4 • R = 0) :
    w ((4 * Fintype.card H : ℕ) : K) ^ 2 * w (translatedSum H T R) ≤ 1 := by
  set N : ℕ := 4 * Fintype.card H with hNdef
  have hN : 1 ≤ N := Nat.mul_pos (by decide) Fintype.card_pos
  have hNT : N • T = 0 := by rw [hNdef, mul_nsmul, hT, nsmul_zero]
  have hNR : N • R = 0 := by rw [hNdef, mul_nsmul, hR, nsmul_zero]
  have hNQ (Q : H) : N • (Q : W.toAffine.Point) = 0 := by
    have hQ : Fintype.card H • (Q : W.toAffine.Point) = 0 := by
      have h := congrArg Subtype.val (card_nsmul_eq_zero (x := Q))
      simpa only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] using h
    rw [hNdef, Nat.mul_comm, mul_nsmul, hQ, nsmul_zero]
  have hterm (Q : H) :
      w ((N : K) ^ 2 * (xCoordinate (T + (Q : W.toAffine.Point)) -
        xCoordinate (R + (Q : W.toAffine.Point)))) ≤ 1 := by
    have ht := apply_xCoordinate_le_of_notMem_modelBadPlaces w W hw hN
      (T + (Q : W.toAffine.Point)) (by rw [nsmul_add, hNT, hNQ, zero_add])
    have hr := apply_xCoordinate_le_of_notMem_modelBadPlaces w W hw hN
      (R + (Q : W.toAffine.Point)) (by rw [nsmul_add, hNR, hNQ, zero_add])
    rw [mul_sub, sub_eq_add_neg]
    refine (FinitePlace.add_le w _ _).trans (max_le ?_ ?_)
    · simpa only [map_mul, map_pow] using ht
    · simpa only [map_neg_eq_map, map_mul, map_pow] using hr
  have hsum := apply_sum_le w Finset.univ
    (fun Q : H => (N : K) ^ 2 * (xCoordinate (T + (Q : W.toAffine.Point)) -
      xCoordinate (R + (Q : W.toAffine.Point)))) (by norm_num) (fun Q _ => hterm Q)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, map_mul, map_pow] at hsum
  exact hsum

end JoshiTeich.Act1Scene1.IutTorsionNewton

namespace JoshiTeich.Act1Scene1.IutFourTorsion

open WeierstrassCurve NumberField IutTorsionNewton
open scoped Classical

universe u
variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

/-- Actual four-torsion pairs have Newton sum bounds in their coordinate number field. -/
theorem pointPairsBounds_over_field
    (H : letI : DecidableEq ↥(field E Fbar) := Classical.decEq _
      AddSubgroup (E.map (algebraMap F ↥(field E Fbar))).toAffine.Point) [Fintype H] :
    letI : DecidableEq ↥(field E Fbar) := Classical.decEq _
    ∃ P : IutFourTorsionPointPairs (E.map (algebraMap F ↥(field E Fbar))),
      ∀ w : FinitePlace ↥(field E Fbar),
        w ∉ modelBadPlaces (E.map (algebraMap F ↥(field E Fbar))) →
        (w ((4 * Fintype.card H : ℕ) : ↥(field E Fbar)) ^ 2 *
          w (translatedSum H P.T₁ P.R₁) ≤ 1) ∧
        (w ((4 * Fintype.card H : ℕ) : ↥(field E Fbar)) ^ 2 *
          w (translatedSum H P.T₂ P.R₂) ≤ 1) := by
  letI : DecidableEq ↥(field E Fbar) := Classical.decEq _
  obtain ⟨P⟩ := pointPairs_over_field E Fbar
  exact ⟨P, fun w hw => ⟨translatedSum_le w H hw P.T₁ P.R₁ P.four_nsmul_T₁ P.four_nsmul_R₁,
    translatedSum_le w H hw P.T₂ P.R₂ P.four_nsmul_T₂ P.four_nsmul_R₂⟩⟩

end JoshiTeich.Act1Scene1.IutFourTorsion
