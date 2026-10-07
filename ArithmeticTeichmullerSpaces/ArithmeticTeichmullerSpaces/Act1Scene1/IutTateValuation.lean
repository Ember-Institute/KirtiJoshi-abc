import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open WithZero
open scoped NumberField Valued

universe u

/-!
source-id: IUT-COR312-TATE-VALUATION
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`,
`valued_eq_of_isUniformizer` and `valued_tateParameter_q`; supporting order
normalization: `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean`,
`TateParameter.norm_q_eq_pow_orderNat`.
fidelity: the contract is completion-valued and keeps the chosen uniformizer,
its certificate, and the Tate parameter explicit. It derives the integer
q-order from the completion valuation, proves the uniformizer norm/order
equation, and proves the valuation law used by q-root transfer. It does not
construct a real `InitialThetaData`, `TateFamily`, q-root, or `V_p^oss`
identification.
boundary: Scene1/Derived
-/

noncomputable def IutBaseQPilotSource.uniformizerQOrder
    {F : Type u} [Field F] [NumberField F]
    {ell : ℕ} (B : IutBaseQPilotSource F ell)
    (π : ∀ w : B.badFinset, w.1.maximalIdeal.adicCompletion F)
    (hπ : ∀ w, Arithmetic.IsCompletionUniformizer w.1 (π w))
    (w : B.badFinset) : ℕ :=
  iutCompletionUniformizerQOrder w.1 (B.tateParameter w)
    (B.tateParameter_ne_zero w) (π w) (hπ w)

lemma iutCompletionUniformizerQOrder_eq_of_norm_eq
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) (hq : q ≠ 0)
    (hqNorm : ‖q‖ < 1)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π)
    (n : ℕ) (hnorm : ‖q‖ = ‖π‖ ^ n) :
    iutCompletionUniformizerQOrder w q hq π hπ = n := by
  apply (pow_right_injective₀ (norm_pos_iff.mpr hπ.ne_zero) hπ.norm_lt_one.ne)
  exact (iutCompletionUniformizerQOrder_norm_eq w q hq hqNorm π hπ).symm.trans hnorm

structure IutCompletionTateValuation
    {F : Type u} [Field F] [NumberField F]
    {ell : ℕ} (B : IutBaseQPilotSource F ell) : Type u where
  /-- The chosen local uniformizer at every base q-pilot place. -/
  uniformizer : ∀ w : B.badFinset, w.1.maximalIdeal.adicCompletion F
  /-- The chosen element satisfies the source-shaped uniformizer contract. -/
  uniformizer_isCompletionUniformizer : ∀ w,
    Arithmetic.IsCompletionUniformizer w.1 (uniformizer w)
  /-- IUT's admissible-prime condition on the order derived from this uniformizer. -/
  orderedQOrder_coprime : ∀ w,
    Nat.Coprime ell
      (B.uniformizerQOrder uniformizer uniformizer_isCompletionUniformizer w)

namespace IutCompletionTateValuation

variable {F : Type u} [Field F] [NumberField F]
variable {ell : ℕ} {B : IutBaseQPilotSource F ell}

/-- Build the completion valuation from the normalized order carried by
`TateParameter.toOrdered`. Its norm law and coprimality condition are the
completion forms of `norm_q_eq_pow_orderNat` and `q_order_coprime`. -/
def ofIutNormalizedOrder
    (uniformizer : ∀ w : B.badFinset, w.1.maximalIdeal.adicCompletion F)
    (hUniformizer : ∀ w,
      Arithmetic.IsCompletionUniformizer w.1 (uniformizer w))
    (sourceOrder : B.badFinset → ℕ)
    (sourceOrder_norm_eq : ∀ w,
      ‖B.tateParameter w‖ = ‖uniformizer w‖ ^ sourceOrder w)
    (sourceOrder_coprime : ∀ w, Nat.Coprime ell (sourceOrder w)) :
    IutCompletionTateValuation B := by
  refine
    { uniformizer := uniformizer
      uniformizer_isCompletionUniformizer := hUniformizer
      orderedQOrder_coprime := ?_ }
  intro w
  have hOrder :
      B.uniformizerQOrder uniformizer hUniformizer w = sourceOrder w := by
    change iutCompletionUniformizerQOrder w.1 (B.tateParameter w)
      (B.tateParameter_ne_zero w) (uniformizer w) (hUniformizer w) = sourceOrder w
    exact iutCompletionUniformizerQOrder_eq_of_norm_eq w.1
      (B.tateParameter w) (B.tateParameter_ne_zero w)
      (B.tateParameter_norm_lt_one w) (uniformizer w) (hUniformizer w)
      (sourceOrder w) (sourceOrder_norm_eq w)
  rw [hOrder]
  exact sourceOrder_coprime w

noncomputable def orderedQOrder
    (C : IutCompletionTateValuation B) (w : B.badFinset) : ℕ :=
  B.uniformizerQOrder C.uniformizer C.uniformizer_isCompletionUniformizer w

lemma ofIutNormalizedOrder_order_eq
    (uniformizer : ∀ w : B.badFinset, w.1.maximalIdeal.adicCompletion F)
    (hUniformizer : ∀ w,
      Arithmetic.IsCompletionUniformizer w.1 (uniformizer w))
    (sourceOrder : B.badFinset → ℕ)
    (sourceOrder_norm_eq : ∀ w,
      ‖B.tateParameter w‖ = ‖uniformizer w‖ ^ sourceOrder w)
    (sourceOrder_coprime : ∀ w, Nat.Coprime ell (sourceOrder w))
    (w : B.badFinset) :
    (ofIutNormalizedOrder (B := B) uniformizer hUniformizer sourceOrder
      sourceOrder_norm_eq sourceOrder_coprime).orderedQOrder w = sourceOrder w := by
  change iutCompletionUniformizerQOrder w.1 (B.tateParameter w)
    (B.tateParameter_ne_zero w) (uniformizer w) (hUniformizer w) = sourceOrder w
  exact iutCompletionUniformizerQOrder_eq_of_norm_eq w.1
    (B.tateParameter w) (B.tateParameter_ne_zero w)
    (B.tateParameter_norm_lt_one w) (uniformizer w) (hUniformizer w)
    (sourceOrder w) (sourceOrder_norm_eq w)

lemma completionQOrder_eq_orderNat
    (C : IutCompletionTateValuation B) (w : B.badFinset) :
    B.qOrder w = C.orderedQOrder w := by
  exact iutCompletionQOrder_eq_of_norm_eq_uniformizer_pow w.1
    (B.tateParameter w) (B.tateParameter_ne_zero w)
    (B.tateParameter_norm_lt_one w) (C.uniformizer w)
    (C.uniformizer_isCompletionUniformizer w) (C.orderedQOrder w)
    (iutCompletionUniformizerQOrder_norm_eq w.1 (B.tateParameter w)
      (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w)
      (C.uniformizer w) (C.uniformizer_isCompletionUniformizer w))

lemma qOrder_coprime
    (C : IutCompletionTateValuation B) (w : B.badFinset) :
    Nat.Coprime ell (B.qOrder w) := by
  rw [C.completionQOrder_eq_orderNat w]
  exact C.orderedQOrder_coprime w

lemma norm_eq_pow_order
    (C : IutCompletionTateValuation B) (w : B.badFinset) :
    ‖B.tateParameter w‖ = ‖C.uniformizer w‖ ^ B.qOrder w :=
  iutCompletionNorm_eq_uniformizer_pow_qOrder w.1 (B.tateParameter w)
    (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w)
    (C.uniformizer w) (C.uniformizer_isCompletionUniformizer w)

lemma valued_tateParameter_eq_exp_neg_order
    (C : IutCompletionTateValuation B) (w : B.badFinset) :
    Valued.v (B.tateParameter w) = exp (-(B.qOrder w : ℤ)) := by
  have hq : B.tateParameter w ≠ 0 := B.tateParameter_ne_zero w
  have hq' : Valued.v (B.tateParameter w) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hq
  set m : ℤ := log (Valued.v (B.tateParameter w))
  have hm : Valued.v (B.tateParameter w) = exp m := (exp_log hq').symm
  have hN : (1 : ℝ) < (Arithmetic.residueChar w.1 : ℝ) ^ Arithmetic.inertDeg w.1 := by
    have hp : (Arithmetic.residueChar w.1).Prime :=
      Arithmetic.residueChar_prime w.1
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt)
      (Arithmetic.inertDeg_pos w.1).ne'
  have h1 := C.norm_eq_pow_order w
  rw [Arithmetic.completionNorm_eq_residueChar_pow_of_valued w.1
      (B.tateParameter w) m hm,
    Arithmetic.completionNorm_eq_residueChar_pow_of_valued w.1
      (C.uniformizer w) (-1)
      (Arithmetic.valued_eq_exp_neg_one_of_isCompletionUniformizer w.1
        (C.uniformizer_isCompletionUniformizer w))] at h1
  set N : ℝ := (Arithmetic.residueChar w.1 : ℝ) ^ Arithmetic.inertDeg w.1 with hN'
  rw [← zpow_natCast, ← zpow_mul] at h1
  have hm_order := zpow_right_injective₀ (zero_lt_one.trans hN) hN.ne' h1
  rw [hm, hm_order]
  congr 1
  ring

end IutCompletionTateValuation

namespace IutTorsionQRootSource

variable {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
variable [Algebra F Kt] {ell : ℕ} {B : IutBaseQPilotSource F ell}

lemma canonical_qroot_ordp_eq_of_tateValuation
    (C : IutCompletionTateValuation B)
    (qroot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (qroot_pow_eq : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      qroot v ^ (2 * ell) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v)))
    (hEll : 0 < ell)
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    Arithmetic.ordp v.1 (qroot v) =
      (B.qOrder (basePlaceOf (B := B) v) : ℝ) /
        (2 * (ell : ℝ) * Arithmetic.ramIdx (basePlaceOf (B := B) v).1) := by
  exact canonical_qroot_ordp_eq B qroot qroot_pow_eq
    (fun w => IutCompletionTateValuation.valued_tateParameter_eq_exp_neg_order C w)
    hEll v

end IutTorsionQRootSource

end JoshiTeich.Act1Scene1
