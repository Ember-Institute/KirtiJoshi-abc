import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotBridge

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
`QPilotData`. Its concrete constructor supplies the weight
`inertDeg / [K : ℚ]`. This adapter keeps those two facts visible at the
Scene1 boundary. It does not construct `InitialThetaData`, `TateFamily`, or
the equality between `badPlacesOver` and the local `AdelicThetaLink` carrier.
-/

structure IutQPilotSource
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  /-- The finite carrier exported by the IUT q-pilot construction. -/
  badFinset : Finset (NumberField.FinitePlace K)
  /-- Adapter obligation: the exported carrier is the Scene1 link carrier. -/
  badFinset_spec : (↑badFinset : Set (NumberField.FinitePlace K)) =
    (↑T.scene1.data.link.places : Set (NumberField.FinitePlace K))
  /-- The normalized arithmetic-degree weight exported by q-pilot data. -/
  weight : NumberField.FinitePlace K → ℝ
  /-- Positivity on the exported bad-place carrier. -/
  weight_pos : ∀ w ∈ badFinset, 0 < weight w
  /-- The concrete `QPilotInputs.qPilot` normalization. -/
  weight_eq_arithmetic : ∀ w, weight w = Arithmetic.qPilotWeight w

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
  have h := Set.ext_iff.mp S.badFinset_spec w
  simpa using h

noncomputable def toSceneQPilot
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    Corollary312QPilotData p T := by
  refine
    { badFinset := S.badFinset
      badFinset_spec := S.badFinset_eq_link_places p
      weight := S.weight
      weight_pos := S.weight_pos
      compatibility := hCompat }

lemma toSceneQPilot_weight_eq_arithmetic
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    ∀ w, (S.toSceneQPilot p hCompat).weight w = Arithmetic.qPilotWeight w := by
  intro w
  exact S.weight_eq_arithmetic w

end IutQPilotSource

end JoshiTeich.Act1Scene1
