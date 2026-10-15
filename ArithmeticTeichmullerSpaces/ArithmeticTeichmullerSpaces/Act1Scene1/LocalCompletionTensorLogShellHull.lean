import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIntegralHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensor

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-LOG-SHELL-HULL
source: Joshi III integral tensor hull and log-shell carrier (3568--3609).
fidelity: proves the actual Z_p integral span of a set already contained in
the ordinary tensor log-shell remains in that shell. This is a carrier
inclusion only; it does not identify the integral hull with a normalization
hull or with a paper theta-volume.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
universe u
noncomputable section

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

theorem integralHull_le_tensorLogShell (U : Set P.Tensor)
    (hU : U ⊆ P.tensorLogShell) :
    P.integralHull U ≤ P.tensorLogShell :=
  (P.integralHull_le_iff U P.tensorLogShell).mpr hU

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
