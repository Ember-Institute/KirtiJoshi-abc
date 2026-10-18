import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionUnramifiedLogShell
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorSaturatedLogShell

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-UNRAMIFIED-LOG-SHELL
source: reference LocalConstruct/LogShell, tensorLogShell_eq_order_of_unramified
and logShell_eq_integral_of_unramified; IUT I Definition 5.4.5.
fidelity: for actual completion packets at an odd prime, factor ramification
indices equal to one give ordinary tensor shell=unit tensor lattice and
normalization-saturated shell=actual normalization. No equality of the
unit tensor order and its normalization is assumed. Original consumer proofs.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance unramIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

omit [Fact p.Prime] [Fintype ι] in
theorem factorLogShell_eq_closedBall_of_unramified (hodd : Odd p) (i : ι)
    (he : Arithmetic.ramIdx (P.place i) = 1) :
    LocalPadicLog.logShell (k := P.Factor i) p = Metric.closedBall (0 : P.Factor i) 1 := by
  simpa only [P.residueChar_eq i] using
    LocalCompletion.logShell_eq_closedBall_of_unramified (P.place i)
      (by rwa [P.residueChar_eq i]) he

omit [Fintype ι] in
theorem tensorLogShell_eq_unitLattice_of_unramified (hodd : Odd p)
    (he : ∀ i, Arithmetic.ramIdx (P.place i) = 1) : P.tensorLogShell = P.unitLattice := by
  unfold tensorLogShell unitLattice
  congr 1
  funext i
  exact P.factorLogShell_eq_closedBall_of_unramified hodd i (he i)

theorem saturatedLogShell_eq_normalization_of_unramified (hodd : Odd p)
    (he : ∀ i, Arithmetic.ramIdx (P.place i) = 1) :
    (P.saturatedLogShell : Set P.Tensor) = P.normalization := by
  apply Set.Subset.antisymm _ P.normalization_subset_saturatedLogShell
  change (P.normalizationHull P.tensorLogShell : Set P.Tensor) ⊆ P.normalization
  rw [P.tensorLogShell_eq_unitLattice_of_unramified hodd he]
  exact P.normalizationHull_subset_normalization _ P.unitLattice_le_normalization

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
