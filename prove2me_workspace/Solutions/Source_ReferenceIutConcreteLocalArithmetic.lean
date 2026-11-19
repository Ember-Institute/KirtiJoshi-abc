/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/LocalConstruct/Arithmetic.lean,
  Iut/Concrete/LocalConstruct/Integral.lean, Iut/Concrete/ThetaLocalConstruct/Ordp.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory
import Solutions.Source_TripodFinitePlaceArithmetic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.RamificationInertia.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField IsDedekindDomain WithZero
open scoped BigOperators WithZero

variable {K : Type*} [Field K] [NumberField K]

lemma ramIdx_pos (w : FinitePlace K) : 0 < ramIdx K w :=
  Tripod.ramIdx_pos' w

lemma localDeg_pos (w : FinitePlace K) : 0 < localDeg K w :=
  Nat.mul_pos (ramIdx_pos w) (Tripod.inertDeg_pos' w)

private lemma span_prime_ne_bot {p : ℕ} (hp : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

private noncomputable def residueCharEquivPrimesOver (p : ℕ) (hp : p.Prime) :
    {w : FinitePlace K // residueChar w = p} ≃ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) where
  toFun w := ⟨w.1.maximalIdeal.asIdeal, w.1.maximalIdeal.isPrime, by
    have h : w.1.maximalIdeal.asIdeal.LiesOver (Ideal.span {(residueChar w.1 : ℤ)}) :=
      Tripod.liesOver_span_residueChar w.1
    exact Eq.mp (congrArg (fun q : ℕ => w.1.maximalIdeal.asIdeal.LiesOver
      (Ideal.span {(q : ℤ)})) w.2) h⟩
  invFun P :=
    let Q : HeightOneSpectrum (𝓞 K) :=
      ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver (span_prime_ne_bot hp) P.2⟩
    ⟨FinitePlace.mk Q, by
      have hover := Ideal.over_def P.1 (Ideal.span {(p : ℤ)})
      have h : (FinitePlace.mk Q).maximalIdeal.asIdeal.under ℤ =
          Ideal.span {(residueChar (FinitePlace.mk Q) : ℤ)} :=
        Tripod.under_int_eq (FinitePlace.mk Q)
      rw [FinitePlace.maximalIdeal_mk] at h
      change P.1.under ℤ = _ at h
      rw [← hover, Ideal.span_singleton_eq_span_singleton] at h
      simpa using (Int.natAbs_eq_iff_associated.mpr h).symm⟩
  left_inv w := by
    apply Subtype.ext
    exact FinitePlace.mk_maximalIdeal w.1
  right_inv P := by
    apply Subtype.ext
    change (FinitePlace.mk (K := K) _).maximalIdeal.asIdeal = P.1
    rw [FinitePlace.maximalIdeal_mk]

private lemma span_prime_isMaximal {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : ℤ)}).IsMaximal := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  exact IsPrime.to_maximal_ideal (span_prime_ne_bot hp)

/-- There are finitely many finite places with any given residue characteristic. -/
theorem fiber_finite (p : ℕ) : Finite {w : FinitePlace K // residueChar w = p} := by
  by_cases hp : p.Prime
  · haveI := span_prime_isMaximal hp
    exact Finite.of_injective _ (residueCharEquivPrimesOver (K := K) p hp).injective
  · haveI : IsEmpty {w : FinitePlace K // residueChar w = p} :=
      ⟨fun w => hp (w.2 ▸ (show (residueChar w.1).Prime from Tripod.residueChar_prime w.1))⟩
    infer_instance

/-- The finite local degrees over a rational prime sum to the absolute degree. -/
theorem sum_localDeg (p : ℕ) (hp : p.Prime) [Fintype {w : FinitePlace K // residueChar w = p}] :
    ∑ w : {w : FinitePlace K // residueChar w = p}, localDeg K w.1 = Module.finrank ℚ K := by
  haveI := span_prime_isMaximal hp
  calc
    _ = ∑ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
          P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ :=
      Fintype.sum_equiv (residueCharEquivPrimesOver (K := K) p hp) _ _ (fun _ => rfl)
    _ = Module.finrank ℤ (𝓞 K) :=
      Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
    _ = Module.finrank ℚ K := RingOfIntegers.rank K

/-- The infinite place multiplicities sum to the absolute degree. -/
theorem sum_mult : ∑ w : InfinitePlace K, w.mult = Module.finrank ℚ K :=
  InfinitePlace.sum_mult_eq

/-- The normalized order is additive on products of nonzero elements. -/
lemma ordp_mul (w : FinitePlace K) (x y : completionAt K w) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordp K w (x * y) = ordp K w x + ordp K w y := by
  unfold ordp
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy), neg_add, add_div]

/-- The discrete valuation of the residue characteristic is the negative ramification index. -/
private lemma intValuation_residueChar (w : FinitePlace K) :
    w.maximalIdeal.intValuation (residueChar w : 𝓞 K) = exp (-(ramIdx K w : ℤ)) := by
  have hp : (residueChar w).Prime := Tripod.residueChar_prime w
  have hp0 : (residueChar w : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmap : (Ideal.span {(residueChar w : ℤ)}).map (algebraMap ℤ (𝓞 K)) =
      Ideal.span {(residueChar w : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hmap0 : (Ideal.span {(residueChar w : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rwa [hmap, ne_eq, Ideal.span_singleton_eq_bot]
  haveI : w.maximalIdeal.asIdeal.LiesOver (Ideal.span {(residueChar w : ℤ)}) :=
    Tripod.liesOver_span_residueChar w
  have hram := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
    (Ideal.span {(residueChar w : ℤ)}) w.maximalIdeal.asIdeal hmap0
  rw [hmap] at hram
  rw [w.maximalIdeal.intValuation_eq_exp_neg_multiplicity hp0, ← hram, ramIdx]

private lemma valued_residueChar (w : FinitePlace K) :
    Valued.v (algebraMap K (completionAt K w) (residueChar w : K)) = exp (-(ramIdx K w : ℤ)) := by
  have hemb : algebraMap K (completionAt K w) (residueChar w : K) =
      FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (residueChar w : 𝓞 K)) := by
    rw [map_natCast (algebraMap (𝓞 K) K)] <;> rfl
  rw [hemb, FinitePlace.embedding_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_residueChar]

/-- The normalized order divides the negative discrete valuation by the ramification index. -/
lemma ordp_eq_of_valued (w : FinitePlace K) (x : completionAt K w) (m : ℤ)
    (hx : Valued.v x = exp m) :
    ordp K w x = -(m : ℝ) / ramIdx K w := by
  have hp : (residueChar w).Prime := Tripod.residueChar_prime w
  have hlog : 0 < Real.log (residueChar w) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hfNat : 0 < inertDeg K w := Tripod.inertDeg_pos' w
  have hf : (0 : ℝ) < inertDeg K w := by exact_mod_cast hfNat
  have hfactor : (inertDeg K w : ℝ) * Real.log (residueChar w) ≠ 0 :=
    mul_ne_zero hf.ne' hlog.ne'
  have hnorm : ‖x‖ = ((residueChar w : ℝ) ^ inertDeg K w) ^ m :=
    Tripod.norm_eq_zpow_of_valued w x m hx
  unfold ordp localDeg
  rw [hnorm, Real.log_zpow, Real.log_pow, Nat.cast_mul,
    neg_mul_eq_neg_mul, mul_assoc (ramIdx K w : ℝ), mul_div_mul_right _ _ hfactor]

/-- The rational residue prime has normalized order one in the completion. -/
lemma ordp_p (w : FinitePlace K) : ordp K w (algebraMap K _ (residueChar w : K)) = 1 := by
  rw [ordp_eq_of_valued w _ _ (valued_residueChar w)]
  have he : (ramIdx K w : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos w).ne'
  rw [Int.cast_neg, Int.cast_natCast, neg_neg, div_self he]

section Different

attribute [local instance] FractionRing.liftAlgebra

/-- A finite place divides the different exactly when its ramification index differs from one. -/
private lemma dvd_differentIdeal_iff_ramIdx_ne_one (w : FinitePlace K) :
    w.maximalIdeal.asIdeal ∣ differentIdeal ℤ (𝓞 K) ↔ ramIdx K w ≠ 1 := by
  rw [ramIdx, dvd_differentIdeal_iff,
    ← Ideal.ramificationIdx_eq_one_iff (q := w.maximalIdeal.asIdeal) (R := ℤ)]

/-- There are finitely many ramified finite places. -/
theorem ramified_finite : {w : FinitePlace K | ramIdx K w ≠ 1}.Finite := by
  classical
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset :
      Set (Ideal (𝓞 K))).Finite := Finset.finite_toSet _
  refine (hfin.preimage (f := fun w : FinitePlace K => w.maximalIdeal.asIdeal) ?_).subset ?_
  · intro w₁ _ w₂ _ h
    exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
  · intro w hw
    rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hD]
    exact ⟨w.maximalIdeal.isPrime,
      Ideal.le_of_dvd ((dvd_differentIdeal_iff_ramIdx_ne_one w).mpr hw)⟩

/-- The different has exponent zero at every unramified finite place. -/
theorem ordDifferent_eq_zero (w : FinitePlace K) (h : ramIdx K w = 1) : ordDifferent K w = 0 := by
  classical
  unfold ordDifferent
  rw [Multiset.count_eq_zero]
  intro hmem
  exact (dvd_differentIdeal_iff_ramIdx_ne_one w).mp
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem) h

end Different

end AbcAdaptation.Reference.Iut.LocalConstruct
