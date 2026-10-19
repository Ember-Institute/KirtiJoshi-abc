import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteCompletionEmbedding
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
source-id: JT-SCENE1-FINITE-COMPLETION-EMBEDDING-TOPOLOGY
source: actual p-adic completion algebras, finite dimensionality and Mathlib
closed embeddings of injective finite-dimensional linear maps.
fidelity: the constructed algebraic embedding into an algebraically closed
normed field is a closed topological embedding when its base map is continuous.
No raw completion isometry is input. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.FiniteCompletionEmbeddingTopology

open JoshiTeich.Prologue NumberField
noncomputable section
universe u
variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {w : FinitePlace K} {v : FinitePlace L}
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
variable {Ω : Type*} [NormedField Ω] [IsAlgClosed Ω]
variable (ι : LocalCompletion.completionAt K w →+* Ω) (hι : Continuous ι)
include hι

theorem isClosedEmbedding : Topology.IsClosedEmbedding (FiniteCompletionEmbedding.embedding hvw ι) := by
  let p := Arithmetic.residueChar w
  let : Fact p.Prime := ⟨Arithmetic.residueChar_prime w⟩
  let hv : Arithmetic.residueChar v = p := Arithmetic.residueChar_eq_of_liesOver hvw
  let := LocalCompletion.padicAlgebra hv
  let := (ι.comp (LocalCompletion.padicEmb (show Arithmetic.residueChar w = p from rfl))).toAlgebra
  let : Module.Finite ℚ_[p] (LocalCompletion.completionAt L v) := LocalCompletion.finite_padicAlgebra hv
  let : ContinuousSMul ℚ_[p] (LocalCompletion.completionAt L v) :=
    continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb hv)
  let : ContinuousSMul ℚ_[p] Ω :=
    continuousSMul_of_algebraMap _ _
      (hι.comp (LocalCompletion.continuous_padicEmb (show Arithmetic.residueChar w = p from rfl)))
  let f : LocalCompletion.completionAt L v →ₗ[ℚ_[p]] Ω :=
    { toFun := FiniteCompletionEmbedding.embedding hvw ι
      map_add' := map_add _
      map_smul' := fun a x => by
        change FiniteCompletionEmbedding.embedding hvw ι (LocalCompletion.padicEmb hv a * x) =
          ι (LocalCompletion.padicEmb (show Arithmetic.residueChar w = p from rfl) a) *
            FiniteCompletionEmbedding.embedding hvw ι x
        rw [map_mul, ← LocalCompletion.embedCompletion_padicEmb hvw rfl,
          FiniteCompletionEmbedding.embedding_base] }
  exact f.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (FiniteCompletionEmbedding.embedding_injective hvw ι))

theorem continuous : Continuous (FiniteCompletionEmbedding.embedding hvw ι) :=
  (isClosedEmbedding hvw ι hι).continuous

end
end JoshiTeich.Act1Scene1.FiniteCompletionEmbeddingTopology
