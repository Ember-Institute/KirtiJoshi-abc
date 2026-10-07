import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

namespace JoshiTeich.Prologue.Theta

/-!
The Tate-parameter boundary records the local parameter function separately
from the theta-link laws.  The source describes a Tate parameter as a
nonzero element with nontrivial finite-place absolute value; the strict
`norm_lt_one` condition is the local Tate-uniformization condition.
-/

structure TateParameterData (K : Type*) [Field K] [NumberField K] where
  places : Finset (NumberField.FinitePlace K)
  /-- The Tate parameter at `w`, as an element of the local completion `K_w`. -/
  parameter : (w : NumberField.FinitePlace K) → w.maximalIdeal.adicCompletion K
  norm : NumberField.FinitePlace K → ℝ
  /-- The normalized integer order of the local Tate parameter.  In `iut` this is
  `OrderedTateParameter.orderNat`; the external ordered-valuation construction is
  intentionally represented here by a carrier field until that infrastructure is
  available in the frozen project. -/
  orderNat : NumberField.FinitePlace K → ℕ

structure TateParameterLaws {K : Type*} [Field K] [NumberField K]
    (T : TateParameterData K) : Prop where
  places_nonempty : T.places.Nonempty
  parameter_nonzero : ∀ w ∈ T.places, T.parameter w ≠ 0
  norm_eq : ∀ w ∈ T.places, T.norm w = ‖T.parameter w‖
  norm_pos : ∀ w ∈ T.places, 0 < T.norm w
  norm_lt_one : ∀ w ∈ T.places, T.norm w < 1
  /-- The normalized Tate order is positive at every represented finite place. -/
  orderNat_pos : ∀ w ∈ T.places, 0 < T.orderNat w

namespace TateParameterData

variable {K : Type*} [Field K] [NumberField K]

/-- The q-order projection ported from `iut`'s `AdmissiblePrimeData.qOrder`. -/
def qOrder (T : TateParameterData K) (w : NumberField.FinitePlace K) : ℕ :=
  T.orderNat w

lemma qOrder_pos (T : TateParameterData K) (hT : TateParameterLaws T)
    (w : NumberField.FinitePlace K) (hw : w ∈ T.places) : 0 < T.qOrder w :=
  hT.orderNat_pos w hw

end TateParameterData

end JoshiTeich.Prologue.Theta
