import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open WithZero
open scoped NumberField Valued

universe u

/-!
source-id: IUT-COR312-Q-SOURCE-CONTRACT
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean`,
and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`.
fidelity: records the separate base-field q-pilot and torsion-field q-root
carriers. The base completion order is derived from the arithmetic API; source
data includes the local parameter and completion comparison map.
boundary: Scene1/Derived
-/

/-- The normalized integer order read from a finite-place completion valuation. -/
noncomputable def iutCompletionQOrder
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) : ℕ :=
  Arithmetic.completionQOrder w q

/-- IUT's integer exponent chosen from the norm generator supplied by a uniformizer. -/
noncomputable def iutCompletionOrderZ
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) (hq : q ≠ 0)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π) : ℤ :=
  Classical.choose (hπ.generates (Units.mk0 q hq))

lemma iutCompletionOrderZ_norm_eq
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) (hq : q ≠ 0)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π) :
    ‖q‖ = ‖π‖ ^ iutCompletionOrderZ w q hq π hπ := by
  simpa [iutCompletionOrderZ] using
    (Classical.choose_spec (hπ.generates (Units.mk0 q hq)))

lemma iutCompletionOrderZ_pos
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) (hq : q ≠ 0)
    (hqNorm : ‖q‖ < 1)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π) :
    0 < iutCompletionOrderZ w q hq π hπ := by
  have hqLog : Real.log ‖q‖ < 0 :=
    Real.log_neg (norm_pos_iff.mpr hq) hqNorm
  have hπLog : Real.log ‖π‖ < 0 :=
    Real.log_neg (norm_pos_iff.mpr hπ.ne_zero) hπ.norm_lt_one
  have hlogEq : Real.log ‖q‖ =
      (iutCompletionOrderZ w q hq π hπ : ℝ) * Real.log ‖π‖ := by
    rw [iutCompletionOrderZ_norm_eq, Real.log_zpow]
  by_contra hnot
  rw [not_lt] at hnot
  have hcast : (iutCompletionOrderZ w q hq π hπ : ℝ) ≤ 0 := by
    exact_mod_cast hnot
  have hnonneg : 0 ≤
      (iutCompletionOrderZ w q hq π hπ : ℝ) * Real.log ‖π‖ := by
    nlinarith [hπLog.le]
  rw [hlogEq] at hqLog
  linarith

/-- The natural order used by IUT's `TateParameter.toOrdered`. -/
noncomputable def iutCompletionUniformizerQOrder
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) (hq : q ≠ 0)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π) : ℕ :=
  Int.toNat (iutCompletionOrderZ w q hq π hπ)

lemma iutCompletionUniformizerQOrder_norm_eq
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) (hq : q ≠ 0)
    (hqNorm : ‖q‖ < 1)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π) :
    ‖q‖ = ‖π‖ ^ iutCompletionUniformizerQOrder w q hq π hπ := by
  have hpos := iutCompletionOrderZ_pos w q hq hqNorm π hπ
  rw [iutCompletionUniformizerQOrder, ← zpow_natCast,
    Int.toNat_of_nonneg hpos.le]
  exact iutCompletionOrderZ_norm_eq w q hq π hπ

structure IutBaseQPilotSource (F : Type u) [Field F] [NumberField F]
    (ell : ℕ) where
  /-- The source bad-place carrier in the base field `F`. -/
  badPlaces : Set (NumberField.FinitePlace F)
  /-- A finite enumeration of the base-field carrier. -/
  badFinset : Finset (NumberField.FinitePlace F)
  badFinset_spec : (↑badFinset : Set (NumberField.FinitePlace F)) = badPlaces
  /-- The arithmetic q-pilot weight is computed in the base field. -/
  weight : NumberField.FinitePlace F → ℝ
  weight_eq_qPilotWeight : ∀ w, weight w = Arithmetic.qPilotWeight w
  /-- The base Tate parameter is a completion element, not a global `F` element. -/
  tateParameter : ∀ w : badFinset, w.1.maximalIdeal.adicCompletion F
  tateParameter_ne_zero : ∀ w, tateParameter w ≠ 0
  tateParameter_norm_lt_one : ∀ w, ‖tateParameter w‖ < 1

lemma iutCompletionQOrder_pos
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F)
    (hq : q ≠ 0) (hqNorm : ‖q‖ < 1) :
    0 < iutCompletionQOrder w q := by
  exact Arithmetic.completionQOrder_pos w q hq hqNorm

lemma iutCompletionQOrder_valued
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F)
    (hq : q ≠ 0) (hqNorm : ‖q‖ < 1) :
    Valued.v q = exp (-(iutCompletionQOrder w q : ℤ)) := by
  exact Arithmetic.completionQOrder_valued w q hq hqNorm

lemma iutCompletionNorm_eq_uniformizer_pow_qOrder
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F)
    (hq : q ≠ 0) (hqNorm : ‖q‖ < 1)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π) :
    ‖q‖ = ‖π‖ ^ iutCompletionQOrder w q := by
  have hqVal := iutCompletionQOrder_valued w q hq hqNorm
  have hπVal := Arithmetic.valued_eq_exp_neg_one_of_isCompletionUniformizer w hπ
  have hqNorm' := Arithmetic.completionNorm_eq_residueChar_pow_of_valued w q
    (-(iutCompletionQOrder w q : ℤ)) hqVal
  have hπNorm := Arithmetic.completionNorm_eq_residueChar_pow_of_valued w π
    (-1 : ℤ) hπVal
  rw [hqNorm', hπNorm]
  change ((Arithmetic.residueChar w : ℝ) ^ Arithmetic.inertDeg w) ^
      (-(iutCompletionQOrder w q : ℤ)) =
    (((Arithmetic.residueChar w : ℝ) ^ Arithmetic.inertDeg w) ^ (-1 : ℤ)) ^
      iutCompletionQOrder w q
  have hpow :
      (((Arithmetic.residueChar w : ℝ) ^ Arithmetic.inertDeg w) ^ (-1 : ℤ)) ^
          iutCompletionQOrder w q =
          ((Arithmetic.residueChar w : ℝ) ^ Arithmetic.inertDeg w) ^
          (-(iutCompletionQOrder w q : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  exact hpow.symm

lemma iutCompletionQOrder_eq_of_norm_eq_uniformizer_pow
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F)
    (hq : q ≠ 0) (hqNorm : ‖q‖ < 1)
    (π : w.maximalIdeal.adicCompletion F)
    (hπ : Arithmetic.IsCompletionUniformizer w π)
    (n : ℕ) (hnorm : ‖q‖ = ‖π‖ ^ n) :
    iutCompletionQOrder w q = n := by
  have hlocal := iutCompletionNorm_eq_uniformizer_pow_qOrder w q hq hqNorm π hπ
  have hpow : ‖π‖ ^ iutCompletionQOrder w q = ‖π‖ ^ n :=
    hlocal.symm.trans hnorm
  exact (pow_right_injective₀ (norm_pos_iff.mpr hπ.ne_zero)
    hπ.norm_lt_one.ne) hpow

namespace IutBaseQPilotSource

variable {F : Type u} [Field F] [NumberField F]
variable {ell : ℕ} (B : IutBaseQPilotSource F ell)

noncomputable def qOrder (w : B.badFinset) : ℕ :=
  iutCompletionQOrder w.1 (B.tateParameter w)

lemma qOrder_pos (w : B.badFinset) : 0 < B.qOrder w :=
  iutCompletionQOrder_pos w.1 (B.tateParameter w)
    (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w)

lemma weight_pos (w : NumberField.FinitePlace F) : 0 < B.weight w := by
  rw [B.weight_eq_qPilotWeight]
  exact Arithmetic.qPilotWeight_pos w

lemma mem_badPlaces (w : B.badFinset) : w.1 ∈ B.badPlaces := by
  have h := Set.ext_iff.mp B.badFinset_spec w.1
  exact h.mp (Finset.mem_coe.mpr w.2)

end IutBaseQPilotSource

structure IutTorsionQRootSource
    (F Kt : Type u) [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] (ell : ℕ) (B : IutBaseQPilotSource F ell) where
  /-- The finite q-root carrier in the torsion field `K_t`. -/
  badFinset : Finset (NumberField.FinitePlace Kt)
  /-- Every torsion carrier place lies over a base-field bad place. -/
  basePlace : ∀ _v : badFinset, B.badFinset
  liesOver : ∀ v : badFinset,
    Ideal.LiesOver v.1.maximalIdeal.asIdeal (basePlace v).1.maximalIdeal.asIdeal
  /-- The q-root is an element of the torsion completion. -/
  qroot : ∀ v : badFinset, v.1.maximalIdeal.adicCompletion Kt
  qroot_ne_zero : ∀ v, qroot v ≠ 0
  /-- Comparison of the two local completions. -/
  completionMap : ∀ v : badFinset,
    (basePlace v).1.maximalIdeal.adicCompletion F →+*
      v.1.maximalIdeal.adicCompletion Kt
  /-- The root equation is stated after base change to the torsion completion. -/
  qroot_pow_eq : ∀ v : badFinset,
    qroot v ^ (2 * ell) =
      completionMap v (B.tateParameter (basePlace v))

end JoshiTeich.Act1Scene1
