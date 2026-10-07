import ArithmeticTeichmullerSpaces.Act1Scene1.IutQPilotAdapter
import ArithmeticTeichmullerSpaces.Prologue.Arithmetic
import Mathlib.NumberTheory.RamificationInertia.Valuation

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open WithZero
open scoped NumberField Valued

universe u

/-!
source-id: IUT-COR312-FIELD-ORIENTATION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean`,
`refer/iut/Iut/Cor312/ThetaData/TateFamily.lean`,
`refer/iut/Iut/Concrete/ThetaRegion.lean`, and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`; local valuation/norm laws in
`Prologue/Arithmetic/Basic.lean`.
fidelity: explicit audit boundary for the base-field q-pilot and the torsion-field
q-root; the base completion's integer q-order is derived from `Valued.v`, and its
uniformizer power law is proved. The IUT normalized order and its coprimality
condition remain explicit source data, and equality with the valuation-derived
order is proved from their shared uniformizer norm law. No `InitialThetaData`
instance is constructed here.
boundary: Scene1/Derived

The reference implementation has three different carriers:

* `QPilotData` enumerates bad places of the base field `F` and uses
  `inertDeg / [F : ℚ]` weights;
* `TateFamily` and `ThetaLocalData.qroot` live at finite places of the torsion
  field `K_t`, with q-roots in completions `K_{t,v}`;
* the comparison from a base completion `F_w` to a torsion completion `K_{t,v}`
  is part of the local source data.

The former `IutQPilotSource` is an adapter over the local Scene1 field and is
not, by itself, an instance of this three-layer source.  The structures below
keep the distinction visible until a real `InitialThetaData` construction is
available.
-/

/-- The normalized integer order read from a finite-place completion valuation. -/
noncomputable def iutCompletionQOrder
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F) : ℕ :=
  Int.toNat (-log (Valued.v q))

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
  have hqv : Valued.v q ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  set m : ℤ := log (Valued.v q)
  have hm : Valued.v q = exp m := (exp_log hqv).symm
  have hp : (Arithmetic.residueChar w).Prime := Arithmetic.residueChar_prime w
  have hN : (1 : ℝ) < (Arithmetic.residueChar w : ℝ) ^ Arithmetic.inertDeg w :=
    one_lt_pow₀ (by exact_mod_cast hp.one_lt)
      (Arithmetic.inertDeg_pos w).ne'
  have hNorm := Arithmetic.completionNorm_eq_residueChar_pow_of_valued w q m hm
  have hmNeg : m < 0 := by
    rw [hNorm] at hqNorm
    rw [zpow_lt_one_iff_right₀ hN] at hqNorm
    exact hqNorm
  have hcast : ((Int.toNat (-m) : ℕ) : ℤ) = -m :=
    Int.toNat_of_nonneg (by omega)
  have hpos : (0 : ℤ) < (Int.toNat (-m) : ℕ) := by
    rw [hcast]
    omega
  unfold iutCompletionQOrder
  rw [show log (Valued.v q) = m from rfl]
  exact_mod_cast hpos

lemma iutCompletionQOrder_valued
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F)
    (q : w.maximalIdeal.adicCompletion F)
    (hq : q ≠ 0) (hqNorm : ‖q‖ < 1) :
    Valued.v q = exp (-(iutCompletionQOrder w q : ℤ)) := by
  have hqv : Valued.v q ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  set m : ℤ := log (Valued.v q)
  have hm : Valued.v q = exp m := (exp_log hqv).symm
  have hqOrderPos := iutCompletionQOrder_pos w q hq hqNorm
  have hp : (Arithmetic.residueChar w).Prime := Arithmetic.residueChar_prime w
  have hN : (1 : ℝ) < (Arithmetic.residueChar w : ℝ) ^ Arithmetic.inertDeg w :=
    one_lt_pow₀ (by exact_mod_cast hp.one_lt)
      (Arithmetic.inertDeg_pos w).ne'
  have hNorm := Arithmetic.completionNorm_eq_residueChar_pow_of_valued w q m hm
  have hmNeg : m < 0 := by
    rw [hNorm] at hqNorm
    rw [zpow_lt_one_iff_right₀ hN] at hqNorm
    exact hqNorm
  have hqOrderInt : (iutCompletionQOrder w q : ℤ) = -m := by
    unfold iutCompletionQOrder
    rw [show log (Valued.v q) = m from rfl]
    exact Int.toNat_of_nonneg (by omega)
  have hmEq : m = -(iutCompletionQOrder w q : ℤ) := by omega
  rw [hm, hmEq]

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
  basePlace : ∀ v : badFinset, B.badFinset
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

structure IutFieldOrientationAudit
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    {F : Type u} [Field F] [NumberField F] [Algebra F K]
  (B : IutBaseQPilotSource F T.ell)
    (R : IutTorsionQRootSource F K T.ell B) where
  /-- The target Scene1 carrier is the torsion-field carrier. -/
  torsionCarrier_eq_link : R.badFinset = T.scene1.data.link.places
  /-- The target's local Tate parameter is the image of the base completion value. -/
  linkParameter_completion_eq : ∀ v : R.badFinset,
    R.completionMap v (B.tateParameter (R.basePlace v)) =
      T.scene1.data.link.tate.parameter v.1

namespace IutFieldOrientationAudit

variable {K : Type u} [Field K] [NumberField K]
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {F : Type u} [Field F] [NumberField F] [Algebra F K]
variable {B : IutBaseQPilotSource F T.ell}
variable {R : IutTorsionQRootSource F K T.ell B}

lemma target_carrier_eq_torsion
    (A : IutFieldOrientationAudit p T B R) :
    R.badFinset = T.scene1.data.link.places :=
  A.torsionCarrier_eq_link

lemma qroot_pow_eq_link_completion
    (A : IutFieldOrientationAudit p T B R) (v : R.badFinset) :
    R.qroot v ^ (2 * T.ell) =
      R.completionMap v (B.tateParameter (R.basePlace v)) := by
  exact R.qroot_pow_eq v

lemma qroot_pow_eq_target_completion
    (A : IutFieldOrientationAudit p T B R) (v : R.badFinset) :
    R.qroot v ^ (2 * T.ell) =
      T.scene1.data.link.tate.parameter v.1 := by
  calc
    R.qroot v ^ (2 * T.ell) =
        R.completionMap v (B.tateParameter (R.basePlace v)) :=
      R.qroot_pow_eq v
    _ = T.scene1.data.link.tate.parameter v.1 :=
      A.linkParameter_completion_eq v

lemma base_weight_is_arithmetic
    (w : NumberField.FinitePlace F) :
    B.weight w = Arithmetic.qPilotWeight w :=
  B.weight_eq_qPilotWeight w

end IutFieldOrientationAudit

end JoshiTeich.Act1Scene1
