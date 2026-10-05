import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-ADAPTER
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean`,
`QPilotData`; `refer/iut/Iut/Concrete/ThetaRegion.lean`,
`QPilotInputs.qPilot`.
fidelity: adapter for the actual q-pilot field shape; the source bad-place
carrier and its identification with the local Scene1 carrier remain explicit
inputs.
boundary: Scene1/Derived

`iut` stores the bad-place enumeration and its positive weights in
`QPilotData`. Its concrete constructor `QPilotInputs.qPilot` supplies the
weight `inertDeg / [K : ℚ]`; this adapter derives that same weight instead of
accepting it as a free field. The source certificate below keeps the actual
`InitialThetaData` obligations visible: the `badPlacesOver` carrier, its
Tate parameter and q-order data, and the identifications with the local
Scene1 carrier are all supplied by the caller. No constructor from a norm-bad
element is provided here.
-/

structure IutQPilotSource
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  /-- The `badPlacesOver` carrier exported by the IUT initial Theta data. -/
  badPlacesOver : Set (NumberField.FinitePlace K)
  /-- Finiteness of the IUT bad-place carrier (`QPilotInputs.bad_finite`). -/
  badPlacesOver_finite : badPlacesOver.Finite
  /-- The Tate parameter attached to each place by the IUT Theta data. -/
  tateParameter : NumberField.FinitePlace K → K
  /-- The normalized integer q-order attached to each bad place. -/
  qOrder : NumberField.FinitePlace K → ℕ
  /-- The IUT q-order is positive on the bad carrier. -/
  qOrder_pos : ∀ w, w ∈ badPlacesOver → 0 < qOrder w
  /-- The Tate parameter is nonzero on the bad carrier. -/
  tateParameter_ne_zero : ∀ w, w ∈ badPlacesOver → tateParameter w ≠ 0
  /-- The finite carrier exported by the IUT q-pilot construction. -/
  badFinset : Finset (NumberField.FinitePlace K)
  /-- The finite enumeration is exactly `badPlacesOver`. -/
  badFinset_spec : (↑badFinset : Set (NumberField.FinitePlace K)) = badPlacesOver
  /-- The IUT bad-place carrier is the Scene1 link carrier. -/
  badPlacesOver_eq_link : badPlacesOver =
    (↑T.scene1.data.link.places : Set (NumberField.FinitePlace K))
  /-- The IUT Tate parameter agrees with the local Tate parameter. -/
  tateParameter_eq_link : ∀ w, w ∈ badPlacesOver →
    tateParameter w = T.scene1.data.link.tate.parameter w
  /-- The IUT q-order agrees with the local Tate q-order. -/
  qOrder_eq_link : ∀ w, w ∈ badPlacesOver →
    qOrder w = T.scene1.data.link.tate.qOrder w
  /-- Uniformizer normalization supplied by the IUT Tate/q-order source. -/
  orderCompatibility : TateOrderNormCompatibility T.scene1.data.link
  /-- IUT normalized degree identifies the uniformizer logarithm with the q-pilot weight. -/
  uniformizer_log_eq_weighted_residueChar_log :
    ∀ w, w ∈ badPlacesOver →
      -Real.log (orderCompatibility.uniformizerNorm w) =
        Arithmetic.qPilotWeight w * Real.log (Arithmetic.residueChar w)

namespace IutQPilotSource

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

lemma badFinset_eq_link_places (S : IutQPilotSource p T) :
    S.badFinset = T.scene1.data.link.places := by
  apply Finset.ext
  intro w
  have h := Set.ext_iff.mp (S.badFinset_spec.trans S.badPlacesOver_eq_link) w
  simpa using h

lemma mem_badPlacesOver_iff_link (S : IutQPilotSource p T)
    (w : NumberField.FinitePlace K) :
    w ∈ S.badPlacesOver ↔ w ∈ T.scene1.data.link.places := by
  change w ∈ S.badPlacesOver ↔ w ∈ (↑T.scene1.data.link.places : Set _)
  rw [S.badPlacesOver_eq_link]

noncomputable def toSceneQPilot
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    Corollary312QPilotData p T := by
  refine
    { badFinset := S.badFinset
      badFinset_spec := S.badFinset_eq_link_places p
      weight := Arithmetic.qPilotWeight
      weight_pos := by
        intro w hw
        exact Arithmetic.qPilotWeight_pos w
      compatibility := hCompat }

lemma source_norm_eq_uniformizer_pow_order
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (w : NumberField.FinitePlace K) (hw : w ∈ S.badPlacesOver) :
    w (S.tateParameter w) =
      S.orderCompatibility.uniformizerNorm w ^ S.qOrder w := by
  rw [S.tateParameter_eq_link w hw]
  have hwLink : w ∈ T.scene1.data.link.places :=
    (S.mem_badPlacesOver_iff_link p w).mp hw
  have hParam := hCompat.parameter_eq w hwLink
  rw [← hParam]
  change T.scene1.data.link.qNorm w = _
  rw [QNormTateCompatibility.norm_eq T.scene1.data.link
    T.scene1.input_laws.tate_parameter hCompat w hwLink]
  rw [S.qOrder_eq_link w hw]
  exact S.orderCompatibility.norm_eq_pow_order w hwLink

lemma toSceneQPilot_sourceNormalization
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    Corollary312QPilotSourceNormalization p T S.orderCompatibility
      (S.toSceneQPilot p hCompat) := by
  refine { uniformizer_log_eq_weighted_residueChar_log := ?_ }
  intro w hw
  have hwBad : w ∈ S.badPlacesOver := by
    have h := hw
    change w ∈ S.badFinset at h
    have hSet : w ∈ (↑S.badFinset : Set (NumberField.FinitePlace K)) :=
      Finset.mem_coe.mpr h
    rw [S.badFinset_spec] at hSet
    exact hSet
  change -Real.log (S.orderCompatibility.uniformizerNorm w) =
    Arithmetic.qPilotWeight w * Real.log (Arithmetic.residueChar w)
  exact S.uniformizer_log_eq_weighted_residueChar_log w hwBad

lemma toSceneQPilot_weight_eq_arithmetic
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    ∀ w, (S.toSceneQPilot p hCompat).weight w = Arithmetic.qPilotWeight w := by
  intro w
  rfl

end IutQPilotSource

end JoshiTeich.Act1Scene1
