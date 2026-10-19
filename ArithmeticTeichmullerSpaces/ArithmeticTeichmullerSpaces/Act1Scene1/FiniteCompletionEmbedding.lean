import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionRelativeDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
source-id: JT-SCENE1-FINITE-COMPLETION-ALGEBRAIC-EMBEDDING
source: actual finite relative completion algebra and Mathlib IsAlgClosed.lift;
Joshi I's local untilt embeddings, Joshi II's local Teichmuller lifts.
fidelity: extends an explicit base-completion embedding to the actual finite
extension completion. No isometry of the raw completion norms is asserted.
Original proofs, no copied reference-engine code; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.FiniteCompletionEmbedding

open JoshiTeich.Prologue NumberField
noncomputable section
universe u
variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {w : FinitePlace K} {v : FinitePlace L}
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
variable (ι : LocalCompletion.completionAt K w →+* Ω)
def embedding : LocalCompletion.completionAt L v →+* Ω := by
  letI := LocalCompletion.relativeAlgebra hvw
  letI := ι.toAlgebra
  letI : Module.Finite (LocalCompletion.completionAt K w) (LocalCompletion.completionAt L v) :=
    LocalCompletion.finite_relativeAlgebra hvw
  exact (IsAlgClosed.lift : LocalCompletion.completionAt L v →ₐ[LocalCompletion.completionAt K w] Ω).toRingHom

theorem embedding_base (x : LocalCompletion.completionAt K w) :
    embedding hvw ι (iutEmbedCompletion hvw x) = ι x := by
  let := LocalCompletion.relativeAlgebra hvw
  let := ι.toAlgebra
  let : Module.Finite (LocalCompletion.completionAt K w) (LocalCompletion.completionAt L v) :=
    LocalCompletion.finite_relativeAlgebra hvw
  exact (IsAlgClosed.lift : LocalCompletion.completionAt L v →ₐ[LocalCompletion.completionAt K w] Ω).commutes x

theorem embedding_injective : Function.Injective (embedding hvw ι) := (embedding hvw ι).injective

end
end JoshiTeich.Act1Scene1.FiniteCompletionEmbedding
