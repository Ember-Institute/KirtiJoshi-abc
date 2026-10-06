import ArithmeticTeichmullerSpaces.Act1Scene1.IutQPilotAdapter

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u

/-!
source-id: IUT-COR312-FIELD-ORIENTATION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`refer/iut/Iut/Cor312/ThetaData/TateFamily.lean`,
`refer/iut/Iut/Concrete/ThetaRegion.lean`, and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`.
fidelity: explicit audit boundary for the base-field q-pilot and the torsion-field
q-root; no `InitialThetaData` instance is constructed here.
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
  /-- The normalized Tate order and its admissible-prime condition. -/
  qOrder : ∀ w : badFinset, ℕ
  qOrder_pos : ∀ w, 0 < qOrder w
  qOrder_coprime : ∀ w, Nat.Coprime ell (qOrder w)

namespace IutBaseQPilotSource

variable {F : Type u} [Field F] [NumberField F]
variable {ell : ℕ} (B : IutBaseQPilotSource F ell)

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
  /-- The target's global Tate parameter has an explicit completion image. -/
  linkParameter_completion_eq : ∀ v : R.badFinset,
    R.completionMap v (B.tateParameter (R.basePlace v)) =
      NumberField.FinitePlace.embedding v.1.maximalIdeal
        (T.scene1.data.link.tate.parameter v.1)

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
      NumberField.FinitePlace.embedding v.1.maximalIdeal
        (T.scene1.data.link.tate.parameter v.1) := by
  rw [R.qroot_pow_eq v]
  exact A.linkParameter_completion_eq v

lemma base_weight_is_arithmetic
    (w : NumberField.FinitePlace F) :
    B.weight w = Arithmetic.qPilotWeight w :=
  B.weight_eq_qPilotWeight w

end IutFieldOrientationAudit

end JoshiTeich.Act1Scene1
