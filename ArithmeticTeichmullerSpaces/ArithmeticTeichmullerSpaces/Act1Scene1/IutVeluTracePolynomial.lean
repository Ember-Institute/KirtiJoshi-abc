import ArithmeticTeichmullerSpaces.Act1Scene1.IutVeluAdditiveTrace
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.ComputeDegree

/-!
source-id: LOCAL-COR312-VELU-TRACE-FACTORIZATION
source: frozen Mathlib polynomial roots, degrees and point-group APIs.
fidelity: local proofs construct the actual trace numerator, identify its
roots with a subgroup coset, and derive the multiplicative Vélu identity.
No Heights code is copied or imported. Local and archimedean estimates remain
separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutVeluPolynomial

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open IutCyclicVelu IutTorsionNewton IutVeluTrace
open scoped Classical

noncomputable section

variable {K : Type*} [Field K] (W : WeierstrassCurve K)
variable (H : AddSubgroup W.toAffine.Point) [Fintype H]

@[simp] lemma xCoordinate_neg (P : W.toAffine.Point) : xCoordinate (-P) = xCoordinate P := by
  cases P with
  | zero => rfl
  | some x y h => rw [Point.neg_some]; rfl

lemma neg_ne_self (hodd : Odd (Fintype.card H)) (Q : H) (hQ : Q ≠ 0) : -Q ≠ Q := by
  intro h
  apply hQ
  apply Subtype.ext
  apply eq_zero_of_add_self H hodd Q.2
  have h' := congrArg Subtype.val h
  change -(Q : W.toAffine.Point) = Q.1 at h'
  calc
    (Q : W.toAffine.Point) + Q.1 = -Q.1 + Q.1 := by rw [h']
    _ = 0 := neg_add_cancel _

/-- The denominator includes every actual nonzero subgroup coordinate. -/
def denominator : K[X] := ∏ Q ∈ nonzeroPoints H, (X - C (xCoordinate Q.1))

/-- Remove the two factors contributed by a point and its negative. -/
def denominatorWithoutPair (Q : H) : K[X] :=
  ∏ S ∈ ((nonzeroPoints H).erase Q).erase (-Q), (X - C (xCoordinate S.1))

/-- The polynomial form of the pair numerator already proved from point addition. -/
def pairPolynomial (q : K) : K[X] :=
  C (2 * q) * (X - C q) ^ 2 + C (6 * q ^ 2 + W.b₂ * q + W.b₄) * (X - C q) +
    C (4 * q ^ 3 + W.b₂ * q ^ 2 + 2 * W.b₄ * q + W.b₆)

/-- The monic numerator of the actual coordinate trace minus a scalar. -/
def numerator (c : K) : K[X] := (X - C c) * denominator W H +
  C ((2 : K)⁻¹) * ∑ Q ∈ nonzeroPoints H,
    pairPolynomial W (xCoordinate Q.1) * denominatorWithoutPair W H Q

lemma monic_denominator : (denominator W H).Monic := monic_prod_X_sub_C _ _

lemma degree_denominator : (denominator W H).natDegree = (nonzeroPoints H).card := by
  rw [denominator, natDegree_prod_of_monic (s := nonzeroPoints H)
    (f := fun Q : H => (X - C (xCoordinate Q.1) : K[X]))
    (h := fun Q _ => monic_X_sub_C (xCoordinate Q.1))]
  simp

lemma nonzeroPoints_card : (nonzeroPoints H).card + 1 = Fintype.card H := by
  have hs : nonzeroPoints H = (Finset.univ : Finset H).erase 0 := by
    ext Q; simp [mem_nonzeroPoints]
  rw [hs]
  exact Finset.card_erase_add_one (Finset.mem_univ (0 : H))

lemma denominator_pair (hodd : Odd (Fintype.card H)) (Q : H)
    (hQ : Q ∈ nonzeroPoints H) :
    denominator W H = (X - C (xCoordinate Q.1)) ^ 2 * denominatorWithoutPair W H Q := by
  have hQ0 := (mem_nonzeroPoints H).mp hQ
  have hnQ : -Q ∈ (nonzeroPoints H).erase Q := by
    simp only [Finset.mem_erase, mem_nonzeroPoints]
    exact ⟨neg_ne_self W H hodd Q hQ0, neg_ne_zero.mpr hQ0⟩
  unfold denominator denominatorWithoutPair
  rw [← Finset.mul_prod_erase (nonzeroPoints H) _ hQ,
    ← Finset.mul_prod_erase ((nonzeroPoints H).erase Q) _ hnQ]
  simp only [AddSubgroup.coe_neg, xCoordinate_neg]
  ring

lemma degree_withoutPair (hodd : Odd (Fintype.card H)) (Q : H)
    (hQ : Q ∈ nonzeroPoints H) :
    (denominatorWithoutPair W H Q).natDegree + 2 = (nonzeroPoints H).card := by
  have hQ0 := (mem_nonzeroPoints H).mp hQ
  have hnQ : -Q ∈ (nonzeroPoints H).erase Q := by
    simp only [Finset.mem_erase, mem_nonzeroPoints]
    exact ⟨neg_ne_self W H hodd Q hQ0, neg_ne_zero.mpr hQ0⟩
  have hc₁ := Finset.card_erase_add_one hQ
  have hc₂ := Finset.card_erase_add_one hnQ
  unfold denominatorWithoutPair
  have hd0 := natDegree_prod_of_monic
    (s := ((nonzeroPoints H).erase Q).erase (-Q))
    (f := fun S : H => (X - C (xCoordinate S.1) : K[X]))
    (h := fun S _ => monic_X_sub_C (xCoordinate S.1))
  have hd : (∏ S ∈ ((nonzeroPoints H).erase Q).erase (-Q),
      (X - C (xCoordinate S.1) : K[X])).natDegree =
      (((nonzeroPoints H).erase Q).erase (-Q)).card := by
    simpa [natDegree_X_sub_C] using hd0
  rw [hd]
  omega

lemma degree_pairPolynomial (q : K) : (pairPolynomial W q).natDegree ≤ 2 := by
  unfold pairPolynomial
  compute_degree!

lemma numerator_monic_degree (hodd : Odd (Fintype.card H)) (c : K) :
    (numerator W H c).Monic ∧ (numerator W H c).natDegree = Fintype.card H := by
  have hmain : ((X - C c) * denominator W H).Monic :=
    (monic_X_sub_C c).mul (monic_denominator W H)
  have hdmain : ((X - C c) * denominator W H).natDegree = (nonzeroPoints H).card + 1 := by
    rw [natDegree_mul (monic_X_sub_C c).ne_zero (monic_denominator W H).ne_zero,
      natDegree_X_sub_C, degree_denominator]
    omega
  have hs : (∑ Q ∈ nonzeroPoints H,
      pairPolynomial W (xCoordinate Q.1) * denominatorWithoutPair W H Q).natDegree ≤
      (nonzeroPoints H).card := by
    apply natDegree_sum_le_of_forall_le
    intro Q hQ
    have hd := degree_withoutPair W H hodd Q hQ
    exact (natDegree_mul_le.trans (Nat.add_le_add_right (degree_pairPolynomial W _) _)).trans
      (by omega)
  have hsmall : (C ((2 : K)⁻¹) * ∑ Q ∈ nonzeroPoints H,
      pairPolynomial W (xCoordinate Q.1) * denominatorWithoutPair W H Q).natDegree <
      ((X - C c) * denominator W H).natDegree := by
    calc
      _ ≤ (∑ Q ∈ nonzeroPoints H,
        pairPolynomial W (xCoordinate Q.1) * denominatorWithoutPair W H Q).natDegree :=
          natDegree_C_mul_le _ _
      _ ≤ (nonzeroPoints H).card := hs
      _ < _ := by rw [hdmain]; omega
  constructor
  · exact hmain.add_of_left (degree_lt_degree hsmall)
  · rw [numerator, natDegree_add_eq_left_of_natDegree_lt hsmall, hdmain, nonzeroPoints_card]

@[simp] lemma eval_pairPolynomial (q z : K) :
    (pairPolynomial W q).eval z = pairNumerator W z q := by
  simp [pairPolynomial, pairNumerator]

lemma eval_denominator_ne_zero (P : W.toAffine.Point) (hP : P ∉ H) :
    (denominator W H).eval (xCoordinate P) ≠ 0 := by
  rw [denominator, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro Q hQ
  simp only [eval_sub, eval_X, eval_C]
  apply sub_ne_zero.mpr
  exact xCoordinate_ne_of_notMem H hP Q.2 fun h =>
    (mem_nonzeroPoints H).mp hQ (Subtype.ext h)

/-- Evaluation of the constructed numerator gives the actual coordinate sum. -/
theorem eval_numerator (h2 : (2 : K) ≠ 0) (hodd : Odd (Fintype.card H))
    (c : K) (P : W.toAffine.Point) (hP : P ∉ H) :
    (numerator W H c).eval (xCoordinate P) =
      ((∑ Q : H, xCoordinate (P + Q.1)) - c) * (denominator W H).eval (xCoordinate P) := by
  let z := xCoordinate P
  have hterm (Q : H) (hQ : Q ∈ nonzeroPoints H) :
      pairNumerator W z (xCoordinate Q.1) * (denominatorWithoutPair W H Q).eval z =
      (2 * xCoordinate Q.1 + pairCorrection W z (xCoordinate Q.1)) *
        (denominator W H).eval z := by
    have hd : z - xCoordinate Q.1 ≠ 0 := sub_ne_zero.mpr
      (xCoordinate_ne_of_notMem H hP Q.2 fun h =>
        (mem_nonzeroPoints H).mp hQ (Subtype.ext h))
    rw [denominator_pair W H hodd Q hQ]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, pairCorrection]
    field_simp [hd]
    ring
  change (numerator W H c).eval z = _
  simp only [numerator, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    eval_finsetSum, eval_pairPolynomial]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have ht := traceFunction_eq W H h2 P hP
  change 2 * z + ∑ Q ∈ nonzeroPoints H,
    (2 * xCoordinate Q.1 + pairCorrection W z (xCoordinate Q.1)) =
      2 * ∑ Q : H, xCoordinate (P + Q.1) at ht
  have hs : (∑ Q ∈ nonzeroPoints H,
      (2 * xCoordinate Q.1 + pairCorrection W z (xCoordinate Q.1))) =
      2 * (∑ Q : H, xCoordinate (P + Q.1)) - 2 * z := by linear_combination ht
  rw [hs]
  field_simp [h2]
  ring

/-- Translation in the subgroup preserves the actual coordinate trace. -/
lemma sum_translate (P : W.toAffine.Point) (Q₀ : H) :
    (∑ Q : H, xCoordinate ((P + Q₀.1) + Q.1)) = ∑ Q : H, xCoordinate (P + Q.1) := by
  apply Fintype.sum_equiv (Equiv.addLeft Q₀)
  intro Q
  change xCoordinate ((P + Q₀.1) + Q.1) = xCoordinate (P + (Q₀ + Q).1)
  rw [AddSubgroup.coe_add, add_assoc]

lemma coset_notMem (R : W.toAffine.Point) (hR : R ∉ H) (Q : H) : R + Q.1 ∉ H := by
  intro h
  have hm := H.sub_mem h Q.2
  exact hR (by simpa using hm)

/-- If twice R is outside H, the coset has pairwise different x coordinates. -/
lemma coset_x_injective (R : W.toAffine.Point) (hR : R ∉ H) (hRR : R + R ∉ H) :
    Function.Injective (fun Q : H => xCoordinate (R + Q.1)) := by
  intro Q S h
  have hQ0 : R + Q.1 ≠ 0 := fun hz => coset_notMem W H R hR Q (hz ▸ H.zero_mem)
  have hS0 : R + S.1 ≠ 0 := fun hz => coset_notMem W H R hR S (hz ▸ H.zero_mem)
  rcases eq_or_eq_neg_of_xCoordinate_eq hQ0 hS0 h with heq | hneg
  · apply Subtype.ext
    exact add_left_cancel heq
  · apply (hRR ?_).elim
    have heq : R + R = -(Q.1 + S.1) := by
      have hh : (R + Q.1) + (R + S.1) = 0 := by rw [hneg, neg_add_cancel]
      apply eq_neg_of_add_eq_zero_left
      calc
        (R + R) + (Q.1 + S.1) = (R + Q.1) + (R + S.1) := by abel
        _ = 0 := hh
    rw [heq]
    exact H.neg_mem (H.add_mem Q.2 S.2)

/-- The coset coordinates are all the roots of the monic actual trace numerator. -/
theorem numerator_factorization (h2 : (2 : K) ≠ 0) (hodd : Odd (Fintype.card H))
    (R : W.toAffine.Point) (hR : R ∉ H) (hRR : R + R ∉ H) :
    numerator W H (∑ Q : H, xCoordinate (R + Q.1)) =
      ∏ Q : H, (X - C (xCoordinate (R + Q.1))) := by
  let f : H → K := fun Q => xCoordinate (R + Q.1)
  let S := Finset.univ.image f
  have hf : Function.Injective f := coset_x_injective W H R hR hRR
  let N := numerator W H (∑ Q : H, xCoordinate (R + Q.1))
  obtain ⟨hmonic, hdeg⟩ := numerator_monic_degree W H hodd (∑ Q : H, xCoordinate (R + Q.1))
  have hcard : S.card = Fintype.card H := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
  have hroot (a : K) (ha : a ∈ S) : N.eval a = 0 := by
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp ha
    rw [eval_numerator W H h2 hodd _ _ (coset_notMem W H R hR Q), sum_translate]
    simp
  have hroots : N.roots = S.val :=
    roots_eq_of_natDegree_le_card_of_ne_zero hroot (by rw [hdeg, hcard]) hmonic.ne_zero
  have hcount : N.roots.card = N.natDegree := by rw [hroots]; exact hcard.trans hdeg.symm
  have heq := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcount
  rw [hroots] at heq
  change (∏ a ∈ S, (X - C a)) = N at heq
  dsimp only [S] at heq
  rw [Finset.prod_image (fun Q _ T _ h => hf h)] at heq
  exact heq.symm

/-- The actual coordinate-sum difference equals the full coset product divided by the denominator. -/
theorem cosetProduct_eq (h2 : (2 : K) ≠ 0) (hodd : Odd (Fintype.card H))
    (P R : W.toAffine.Point) (hP : P ∉ H) (hR : R ∉ H) (hRR : R + R ∉ H) :
    (∏ Q : H, (xCoordinate P - xCoordinate (R + Q.1))) =
      translatedSum H P R * ∏ Q ∈ nonzeroPoints H, (xCoordinate P - xCoordinate Q.1) := by
  have he := congrArg (Polynomial.eval (xCoordinate P))
    (numerator_factorization W H h2 hodd R hR hRR)
  rw [eval_numerator W H h2 hodd _ P hP] at he
  simpa only [translatedSum, denominator, eval_prod, eval_sub, eval_X, eval_C] using he.symm

/-- The full Vélu additive identity follows from the actual trace factorization. -/
theorem veluRatio_mul (h2 : (2 : K) ≠ 0) (hodd : Odd (Fintype.card H))
    (T R : W.toAffine.Point) (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    veluRatio H T R * (xCoordinate T - xCoordinate R) = translatedSum H T R := by
  have hT := notMem_of_add_self H hodd hT0 hT2
  have hR : R ∉ H := fun h => hT (hRT ▸ H.add_mem h h)
  have hRR : R + R ∉ H := hRT ▸ hT
  have hb := eval_denominator_ne_zero W H T hT
  simp only [denominator, eval_prod, eval_sub, eval_X, eval_C] at hb
  have hprod := cosetProduct_eq W H h2 hodd T R hT hR hRR
  have hs : nonzeroPoints H = (Finset.univ : Finset H).erase 0 := by
    ext Q; simp [mem_nonzeroPoints]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun Q : H => xCoordinate T - xCoordinate (R + Q.1)) (Finset.mem_univ (0 : H))] at hprod
  simp only [ZeroMemClass.coe_zero, add_zero, ← hs] at hprod
  rw [veluRatio, Finset.prod_div_distrib, div_mul_eq_mul_div, div_eq_iff hb]
  simpa only [mul_comm] using hprod

/-- The actual ratio now has the Newton bound at each place outside the model exceptions. -/
theorem crude_bound [NumberField K] (w : NumberField.FinitePlace K)
    (hw : w ∉ modelBadPlaces W) (hodd : Odd (Fintype.card H))
    (T R : W.toAffine.Point) (hT0 : T ≠ 0) (hT2 : T + T = 0) (hRT : R + R = T) :
    w (veluRatio H T R) * w (xCoordinate T - xCoordinate R) *
      w ((4 * Fintype.card H : ℕ) : K) ^ 2 ≤ 1 := by
  have hT4 : 4 • T = 0 := by
    have hT : 2 • T = 0 := by simpa only [two_nsmul] using hT2
    rw [show 4 = 2 * 2 by decide, mul_nsmul, hT, nsmul_zero]
  have hR4 : 4 • R = 0 := by
    have hR : 2 • R = T := by simpa only [two_nsmul] using hRT
    rw [show 4 = 2 * 2 by decide, mul_nsmul, hR, two_nsmul, hT2]
  have h := translatedSum_le w H hw T R hT4 hR4
  rw [← veluRatio_mul W H two_ne_zero hodd T R hT0 hT2 hRT, map_mul] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end
end JoshiTeich.Act1Scene1.IutVeluPolynomial

namespace JoshiTeich.Act1Scene1.IutCyclicCoordinate

open WeierstrassCurve NumberField IutCyclicVelu IutTorsionNewton IutVeluPolynomial
open scoped Classical

universe u
noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))) [Fintype H]

local instance : DecidableEq ↥(field E Fbar H) := Classical.decEq _

/-- The canonical ratio product and the same actual sums satisfy the finite-place crude bound. -/
theorem pointPairs_ratioNewton (hodd : Odd (Fintype.card H))
    (w : FinitePlace ↥(field E Fbar H))
    (hw : w ∉ modelBadPlaces (E.map (algebraMap F ↥(field E Fbar H)))) :
    let G := subgroup E Fbar H
    let P := pointPairs E Fbar H
    (veluRatio G P.T₁ P.R₁ * (xCoordinate P.T₁ - xCoordinate P.R₁) =
      translatedSum G P.T₁ P.R₁) ∧
    (veluRatio G P.T₂ P.R₂ * (xCoordinate P.T₂ - xCoordinate P.R₂) =
      translatedSum G P.T₂ P.R₂) ∧
    w (ratioProduct E Fbar H) * w (xCoordinate P.T₁ - xCoordinate P.R₁) *
      w (xCoordinate P.T₂ - xCoordinate P.R₂) *
        w ((4 * Fintype.card H : ℕ) : ↥(field E Fbar H)) ^ 4 ≤ 1 := by
  let W := E.map (algebraMap F ↥(field E Fbar H))
  let G := subgroup E Fbar H
  let P := pointPairs E Fbar H
  have hoddG : Odd (Fintype.card G) := by simpa only [G, card_subgroup] using hodd
  refine ⟨veluRatio_mul W G two_ne_zero hoddG P.T₁ P.R₁ P.T₁_ne_zero
      P.T₁_add_self P.R₁_add_self,
    veluRatio_mul W G two_ne_zero hoddG P.T₂ P.R₂ P.T₂_ne_zero
      P.T₂_add_self P.R₂_add_self, ?_⟩
  have h₁ := crude_bound W G w hw hoddG P.T₁ P.R₁ P.T₁_ne_zero P.T₁_add_self P.R₁_add_self
  have h₂ := crude_bound W G w hw hoddG P.T₂ P.R₂ P.T₂_ne_zero P.T₂_add_self P.R₂_add_self
  dsimp only [W, G] at h₁ h₂
  rw [card_subgroup] at h₁ h₂
  have hprod := mul_le_one₀ h₁ (by positivity) h₂
  convert hprod using 1 <;> simp only [ratioProduct, map_mul] <;> ring

end
end JoshiTeich.Act1Scene1.IutCyclicCoordinate
