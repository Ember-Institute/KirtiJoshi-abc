import ArithmeticTeichmullerSpaces.Prologue.Interfaces.Carriers

namespace JoshiTeich.Prologue.Theta

/-!
The theta-pilot law isolates the valuation scaling supplied by the primitive
ansatz.  The scale is data, while the `j^2` relation remains a proposition.
No theta-volume estimate is part of this boundary.
-/

structure ThetaPilotScalingLaws {K : Type*} [Field K]
    (P : ThetaPilotData K) (base : P.index) : Prop where
  base_scalingIndex : P.scalingIndex base = 1
  value_nonzero : ∀ i, P.value i ≠ 0
  norm_positive : ∀ i, 0 < P.norm i
  norm_scaling : ∀ i,
    P.norm i = P.norm base ^ (P.scalingIndex i * P.scalingIndex i)

end JoshiTeich.Prologue.Theta
