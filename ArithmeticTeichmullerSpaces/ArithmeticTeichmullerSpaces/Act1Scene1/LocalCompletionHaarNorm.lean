import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarIndex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
source-id: JT-SCENE1-LOCAL-HAAR-NORM
source: Joshi III `le:volume-lemma1`; Mathlib global integer approximation,
prime-ideal quotient cardinality and the completion valuation norm.
fidelity: identifies normalized scalar integral-ball Haar measure with
the current completion norm by an actual quotient isomorphism. Paper norm
renormalization and tensor/theta-locus realization remain separate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField IsDedekindDomain MeasureTheory
open JoshiTeich.Prologue.Arithmetic
open WithZero
open scoped Valued

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K]

/-- The actual global integers map into the completion's integer ring. -/
def globalIntegerMap (w : FinitePlace K) : 𝓞 K →+* integerRing w where
  toFun r := ⟨FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K r),
    Valued.toNormedField.norm_le_one_iff.mp (FinitePlace.norm_le_one K _ r)⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' a b := by ext; simp
  map_mul' a b := by ext; simp

theorem globalIntegerMap_valued (w : FinitePlace K) (r : 𝓞 K) :
    Valued.v (globalIntegerMap w r : completionAt K w) = w.maximalIdeal.intValuation r := by
  change Valued.v (FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K r)) = _
  rw [FinitePlace.embedding_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]

/-- Approximate any integral completion element by a global integer at a nonzero integral radius. -/
theorem exists_globalInteger_norm_sub_lt
    (w : FinitePlace K) (y z : integerRing w) (hz : z ≠ 0) :
    ∃ r : 𝓞 K, ‖(globalIntegerMap w r : completionAt K w) - y‖ < ‖(z : completionAt K w)‖ := by
  have hz0 : (z : completionAt K w) ≠ 0 := Subtype.coe_ne_coe.mpr hz
  have hzv : Valued.v (z : completionAt K w) ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  have hz1 : ‖(z : completionAt K w)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr z.property
  have hy1 : ‖(y : completionAt K w)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr y.property
  obtain ⟨x, hx⟩ := (HeightOneSpectrum.denseRange_algebraMap K w.maximalIdeal).exists_dist_lt
    (y : completionAt K w) (norm_pos_iff.mpr hz0)
  have hx' : ‖(algebraMap K (completionAt K w) x) - y‖ < ‖(z : completionAt K w)‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hx
  have hx1 : ‖(algebraMap K (completionAt K w) x)‖ ≤ 1 := by
    calc
      _ = ‖(algebraMap K (completionAt K w) x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ max ‖algebraMap K (completionAt K w) x - y‖ ‖(y : completionAt K w)‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (hx'.le.trans hz1) hy1
  have hxv : w.maximalIdeal.valuation K x ≤ 1 := by
    have h := Valued.toNormedField.norm_le_one_iff.mp hx1
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using h
  obtain ⟨r, hr⟩ := w.maximalIdeal.exists_valuation_sub_lt_of_integer hxv
    (Units.mk0 (Valued.v (z : completionAt K w)) hzv)
  have hr' : ‖(globalIntegerMap w r : completionAt K w) - algebraMap K (completionAt K w) x‖ <
      ‖(z : completionAt K w)‖ := by
    apply Valued.toNormedField.norm_lt_iff.mpr
    change Valued.v (FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K r) -
      FinitePlace.embedding w.maximalIdeal x) < _
    rw [← map_sub, FinitePlace.embedding_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hr
  refine ⟨r, ?_⟩
  calc
    _ = ‖((globalIntegerMap w r : completionAt K w) - algebraMap K (completionAt K w) x) +
        (algebraMap K (completionAt K w) x - y)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖(globalIntegerMap w r : completionAt K w) - algebraMap K (completionAt K w) x‖
        ‖algebraMap K (completionAt K w) x - y‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < ‖(z : completionAt K w)‖ := max_lt hr' hx'

def principalQuotientMap (w : FinitePlace K) (z : integerRing w) :
    𝓞 K →+* (integerRing w ⧸ Ideal.span {z}) :=
  (Ideal.Quotient.mk (Ideal.span {z})).comp (globalIntegerMap w)

theorem principalQuotientMap_surjective (w : FinitePlace K)
    (z : integerRing w) (hz : z ≠ 0) : Function.Surjective (principalQuotientMap w z) := by
  intro a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨r, hr⟩ := exists_globalInteger_norm_sub_lt w y z hz
  refine ⟨r, ?_⟩
  apply Ideal.Quotient.eq.mpr
  change globalIntegerMap w r - y ∈ (Ideal.span {z} : Set (integerRing w))
  rw [principalIdeal_eq_preimage_closedBall]
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact hr.le

theorem principalQuotientMap_ker (w : FinitePlace K)
    (z : integerRing w) (n : ℕ) (hzv : Valued.v (z : completionAt K w) = exp (-(n : ℤ))) :
    RingHom.ker (principalQuotientMap w z) = w.maximalIdeal.asIdeal ^ n := by
  ext r
  change Ideal.Quotient.mk (Ideal.span {z}) (globalIntegerMap w r) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change globalIntegerMap w r ∈ (Ideal.span {z} : Set (integerRing w)) ↔ _
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  change Valued.v (globalIntegerMap w r : completionAt K w) ≤ Valued.v (z : completionAt K w) ↔ _
  rw [globalIntegerMap_valued, hzv]
  exact w.maximalIdeal.intValuation_le_pow_iff_mem r n

/-- The completed principal quotient is the actual global prime-power quotient. -/
def principalQuotientEquiv (w : FinitePlace K) (z : integerRing w) (hz : z ≠ 0)
    (n : ℕ) (hzv : Valued.v (z : completionAt K w) = exp (-(n : ℤ))) :
    (𝓞 K ⧸ w.maximalIdeal.asIdeal ^ n) ≃+* (integerRing w ⧸ Ideal.span {z}) :=
  (Ideal.quotEquivOfEq (principalQuotientMap_ker w z n hzv).symm).trans
    ((principalQuotientMap w z).quotientKerEquivOfSurjective (principalQuotientMap_surjective w z hz))

theorem principalIndex_eq_absNorm_pow (w : FinitePlace K) (z : integerRing w) (hz : z ≠ 0)
    (n : ℕ) (hzv : Valued.v (z : completionAt K w) = exp (-(n : ℤ))) :
    principalIndex w z = Ideal.absNorm w.maximalIdeal.asIdeal ^ n := by
  change Submodule.cardQuot (Ideal.span {z}) = _
  rw [Submodule.cardQuot_apply, ← Nat.card_congr (principalQuotientEquiv w z hz n hzv).toEquiv]
  change Ideal.absNorm (w.maximalIdeal.asIdeal ^ n) = _
  exact map_pow _ _ _

/-- The real value of the normalized Haar measure equals the completion norm. -/
theorem normalizedHaar_scalarBall_toReal_eq_norm (w : FinitePlace K)
    (z : integerRing w) (hz : z ≠ 0) (n : ℕ)
    (hzv : Valued.v (z : completionAt K w) = exp (-(n : ℤ))) :
    (normalizedHaar w ((fun x : completionAt K w => (z : completionAt K w)*x) ''
      Metric.closedBall 0 1)).toReal = ‖(z : completionAt K w)‖ := by
  rw [normalizedHaar_scalarBall_eq_inv_index w z hz, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, principalIndex_eq_absNorm_pow w z hz n hzv, Nat.cast_pow]
  rw [completionNorm_eq_residueChar_pow_of_valued w _ _ hzv, zpow_neg, zpow_natCast,
    absNorm_eq_pow_residueChar, Nat.cast_pow]

end
end JoshiTeich.Act1Scene1.LocalCompletion
