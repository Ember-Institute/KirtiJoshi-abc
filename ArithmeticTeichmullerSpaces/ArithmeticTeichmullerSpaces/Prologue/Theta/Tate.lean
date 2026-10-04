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
  parameter : NumberField.FinitePlace K → K
  norm : NumberField.FinitePlace K → ℝ

structure TateParameterLaws {K : Type*} [Field K] [NumberField K]
    (T : TateParameterData K) : Prop where
  places_nonempty : T.places.Nonempty
  parameter_nonzero : ∀ w ∈ T.places, T.parameter w ≠ 0
  norm_eq : ∀ w ∈ T.places, T.norm w = w (T.parameter w)
  norm_pos : ∀ w ∈ T.places, 0 < T.norm w
  norm_lt_one : ∀ w ∈ T.places, T.norm w < 1

end JoshiTeich.Prologue.Theta
