import ArithmeticTeichmullerSpaces.Prologue.Theta.Pilot

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Theta

universe u

theorem thetaPilotLogNormScaling
    {K : Type u} [Field K] {P : ThetaPilotData K} {base : P.index}
    (h : ThetaPilotScalingLaws P base) (i : P.index) :
    Real.log (P.norm i) =
      ((P.scalingIndex i * P.scalingIndex i : ℕ) : ℝ) *
        Real.log (P.norm base) := by
  rw [h.norm_scaling i, Real.log_pow]

end JoshiTeich.Act1Scene1
