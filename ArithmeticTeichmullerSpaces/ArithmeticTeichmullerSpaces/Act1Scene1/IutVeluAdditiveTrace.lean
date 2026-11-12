/-
Compatibility proofs copied from Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean,
commit 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3.
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
license-review: Apache-2.0 header and repository LICENSE reviewed before copying.
modifications: keep only the two needed formulas as private project lemmas.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCyclicCoordinateField

/-!
source-id: LOCAL-COR312-VELU-ADDITIVE-TRACE
source: Mathlib affine point addition and duplication formulas at frozen commit
389347a7c1cfa76f6bd5be2ca35d4cb621610ad3.
fidelity: local proofs express the actual subgroup coordinate trace as a
rational function. The pair numerator follows from the duplication invariant;
negation reindexes the finite trace. No Heights code is copied or imported.
The factorization identifying this trace with the actual ratio remains open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutVeluTrace

open WeierstrassCurve WeierstrassCurve.Affine IutCyclicVelu IutTorsionNewton
open scoped Classical

noncomputable section

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

private lemma addX_of_X_ne_compat {x₁ y₁ x₂ y₂ : K} (hn : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) =
      ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) / (x₁ - x₂) ^ 2 := by
  grind only [Affine.addX, Affine.slope]

private lemma den_duplication_eq_compat {x y : K} (h : W.toAffine.Equation x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
      (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  have Heq := (W.toAffine.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * Heq

/-- The numerator of the sum of the two translated x coordinates. -/
def pairNumerator (z q : K) : K :=
  2 * q * (z - q) ^ 2 + (6 * q ^ 2 + W.b₂ * q + W.b₄) * (z - q) +
    (4 * q ^ 3 + W.b₂ * q ^ 2 + 2 * W.b₄ * q + W.b₆)

/-- The correction to twice the subgroup point's x coordinate. -/
def pairCorrection (z q : K) : K := pairNumerator W z q / (z - q) ^ 2 - 2 * q

private lemma additionNumerators_eq (h2 : (2 : K) ≠ 0)
    {z y q r : K} (hP : W.toAffine.Equation z y) (hQ : W.toAffine.Equation q r) :
    ((y - r) ^ 2 + W.a₁ * (y - r) * (z - q) - (W.a₂ + z + q) * (z - q) ^ 2) +
      ((y - W.toAffine.negY q r) ^ 2 + W.a₁ * (y - W.toAffine.negY q r) * (z - q) -
        (W.a₂ + z + q) * (z - q) ^ 2) = pairNumerator W z q := by
  apply mul_left_cancel₀ h2
  calc
    _ = (2 * y + W.a₁ * z + W.a₃) ^ 2 + (2 * r + W.a₁ * q + W.a₃) ^ 2 -
        (W.a₁ ^ 2 + 4 * W.a₂ + 4 * z + 4 * q) * (z - q) ^ 2 := by
      simp only [negY]
      ring
    _ = (4 * z ^ 3 + W.b₂ * z ^ 2 + 2 * W.b₄ * z + W.b₆) +
        (4 * q ^ 3 + W.b₂ * q ^ 2 + 2 * W.b₄ * q + W.b₆) -
        (W.a₁ ^ 2 + 4 * W.a₂ + 4 * z + 4 * q) * (z - q) ^ 2 := by
      rw [← den_duplication_eq_compat W hP, ← den_duplication_eq_compat W hQ]
    _ = _ := by
      simp only [pairNumerator, b₂]
      ring

/-- Point addition gives the rational expression for a pair of opposite subgroup points. -/
theorem paired_xCoordinates (h2 : (2 : K) ≠ 0) {P Q : W.toAffine.Point}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : xCoordinate P ≠ xCoordinate Q) :
    xCoordinate (P + Q) + xCoordinate (P - Q) =
      2 * xCoordinate Q + pairCorrection W (xCoordinate P) (xCoordinate Q) := by
  cases P with
  | zero => exact (hP rfl).elim
  | some z y hp =>
    cases Q with
    | zero => exact (hQ rfl).elim
    | some q r hq =>
      change z ≠ q at hx
      rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
      change W.toAffine.addX z q (W.toAffine.slope z q y r) +
        W.toAffine.addX z q (W.toAffine.slope z q y (W.toAffine.negY q r)) =
          2 * q + pairCorrection W z q
      rw [addX_of_X_ne_compat W hx, addX_of_X_ne_compat W hx, ← add_div,
        additionNumerators_eq W h2 hp.1 hq.1]
      simp only [pairCorrection]
      ring

variable (H : AddSubgroup W.toAffine.Point) [Fintype H]

/-- A rational function of x with the same doubled trace as the actual subgroup sum. -/
def traceFunction (z : K) : K := 2 * z +
  ∑ Q ∈ nonzeroPoints H,
    (2 * xCoordinate (Q : W.toAffine.Point) + pairCorrection W z (xCoordinate Q.1))

private lemma sum_neg_translate (P : W.toAffine.Point) :
    (∑ Q : H, xCoordinate (P - (Q : W.toAffine.Point))) =
      ∑ Q : H, xCoordinate (P + (Q : W.toAffine.Point)) := by
  apply Fintype.sum_equiv (Equiv.neg H)
  intro Q
  simp only [Equiv.neg_apply, AddSubgroup.coe_neg, sub_eq_add_neg]

/-- The actual coordinate trace equals the rational trace function away from the subgroup. -/
theorem traceFunction_eq (h2 : (2 : K) ≠ 0) (P : W.toAffine.Point) (hP : P ∉ H) :
    traceFunction W H (xCoordinate P) =
      2 * ∑ Q : H, xCoordinate (P + (Q : W.toAffine.Point)) := by
  have hP0 : P ≠ 0 := fun h => hP (h ▸ H.zero_mem)
  have hpair (Q : H) (hQ : Q ∈ nonzeroPoints H) :
      2 * xCoordinate (Q : W.toAffine.Point) + pairCorrection W (xCoordinate P)
        (xCoordinate Q.1) = xCoordinate (P + Q.1) + xCoordinate (P - Q.1) := by
    have hQ0 : (Q : W.toAffine.Point) ≠ 0 := fun h =>
      (mem_nonzeroPoints H).mp hQ (Subtype.ext h)
    exact (paired_xCoordinates W h2 hP0 hQ0 (xCoordinate_ne_of_notMem H hP Q.2 hQ0)).symm
  have hset : nonzeroPoints H = (Finset.univ : Finset H).erase 0 := by
    ext Q
    simp only [mem_nonzeroPoints, Finset.mem_erase, Finset.mem_univ, and_true]
  unfold traceFunction
  rw [Finset.sum_congr rfl hpair, hset]
  have hzero : xCoordinate (P + ((0 : H) : W.toAffine.Point)) +
      xCoordinate (P - ((0 : H) : W.toAffine.Point)) = 2 * xCoordinate P := by
    simp only [ZeroMemClass.coe_zero, add_zero, sub_zero, two_mul]
  rw [← hzero, Finset.add_sum_erase Finset.univ
    (fun Q : H => xCoordinate (P + Q.1) + xCoordinate (P - Q.1))
    (Finset.mem_univ (0 : H)),
    Finset.sum_add_distrib, sum_neg_translate W H]
  ring

/-- Both actual sums in the Newton bound have an explicit rational expression. -/
theorem translatedSum_eq (h2 : (2 : K) ≠ 0) (T R : W.toAffine.Point)
    (hT : T ∉ H) (hR : R ∉ H) :
    2 * translatedSum H T R = traceFunction W H (xCoordinate T) -
      traceFunction W H (xCoordinate R) := by
  rw [traceFunction_eq W H h2 T hT, traceFunction_eq W H h2 R hR]
  simp only [translatedSum, mul_sub]

/-- The rational trace difference inherits the actual Newton bound. -/
theorem traceDifference_le [NumberField K] (w : NumberField.FinitePlace K)
    (hw : w ∉ modelBadPlaces W) (h2 : (2 : K) ≠ 0) (T R : W.toAffine.Point)
    (hT : T ∉ H) (hR : R ∉ H) (hT4 : 4 • T = 0) (hR4 : 4 • R = 0) :
    w ((4 * Fintype.card H : ℕ) : K) ^ 2 *
      w (traceFunction W H (xCoordinate T) - traceFunction W H (xCoordinate R)) ≤ w (2 : K) := by
  rw [← translatedSum_eq W H h2 T R hT hR, map_mul]
  have h := translatedSum_le w H hw T R hT4 hR4
  calc
    _ = w (2 : K) * (w ((4 * Fintype.card H : ℕ) : K) ^ 2 * w (translatedSum H T R)) := by ring
    _ ≤ w (2 : K) * 1 := mul_le_mul_of_nonneg_left h (apply_nonneg w _)
    _ = _ := mul_one _

end
end JoshiTeich.Act1Scene1.IutVeluTrace

namespace JoshiTeich.Act1Scene1.IutCyclicCoordinate

open WeierstrassCurve NumberField IutCyclicVelu IutTorsionNewton IutVeluTrace
open scoped Classical

universe u
noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))) [Fintype H]

local instance : DecidableEq ↥(field E Fbar H) := Classical.decEq _

/-- The same canonical pairs have rational trace expressions and actual Newton bounds. -/
theorem pointPairs_traceNewton (hodd : Odd (Fintype.card H))
    (w : FinitePlace ↥(field E Fbar H))
    (hw : w ∉ modelBadPlaces (E.map (algebraMap F ↥(field E Fbar H)))) :
    let W := E.map (algebraMap F ↥(field E Fbar H))
    let G := subgroup E Fbar H
    let P := pointPairs E Fbar H
    (2 * translatedSum G P.T₁ P.R₁ =
      traceFunction W G (xCoordinate P.T₁) - traceFunction W G (xCoordinate P.R₁)) ∧
    (2 * translatedSum G P.T₂ P.R₂ =
      traceFunction W G (xCoordinate P.T₂) - traceFunction W G (xCoordinate P.R₂)) ∧
    (w ((4 * Fintype.card H : ℕ) : ↥(field E Fbar H)) ^ 2 *
      w (traceFunction W G (xCoordinate P.T₁) - traceFunction W G (xCoordinate P.R₁)) ≤ w 2) ∧
    (w ((4 * Fintype.card H : ℕ) : ↥(field E Fbar H)) ^ 2 *
      w (traceFunction W G (xCoordinate P.T₂) - traceFunction W G (xCoordinate P.R₂)) ≤ w 2) := by
  let W := E.map (algebraMap F ↥(field E Fbar H))
  let G := subgroup E Fbar H
  let P := pointPairs E Fbar H
  have hoddG : Odd (Fintype.card G) := by simpa only [G, card_subgroup] using hodd
  have h2 : (2 : ↥(field E Fbar H)) ≠ 0 := two_ne_zero
  have hT₁ := notMem_of_add_self G hoddG P.T₁_ne_zero P.T₁_add_self
  have hT₂ := notMem_of_add_self G hoddG P.T₂_ne_zero P.T₂_add_self
  have hR₁ : P.R₁ ∉ G := fun h => hT₁ (P.R₁_add_self ▸ G.add_mem h h)
  have hR₂ : P.R₂ ∉ G := fun h => hT₂ (P.R₂_add_self ▸ G.add_mem h h)
  refine ⟨translatedSum_eq W G h2 P.T₁ P.R₁ hT₁ hR₁,
    translatedSum_eq W G h2 P.T₂ P.R₂ hT₂ hR₂, ?_, ?_⟩
  · simpa only [W, G, card_subgroup] using
      traceDifference_le W G w hw h2 P.T₁ P.R₁ hT₁ hR₁ P.four_nsmul_T₁ P.four_nsmul_R₁
  · simpa only [W, G, card_subgroup] using
      traceDifference_le W G w hw h2 P.T₂ P.R₂ hT₂ hR₂ P.four_nsmul_T₂ P.four_nsmul_R₂

end
end JoshiTeich.Act1Scene1.IutCyclicCoordinate
