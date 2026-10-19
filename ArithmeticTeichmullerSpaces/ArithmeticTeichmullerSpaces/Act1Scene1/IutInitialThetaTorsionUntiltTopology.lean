import ArithmeticTeichmullerSpaces.Act1Scene1.ClosedFieldEmbeddingNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteCompletionEmbeddingTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionDeRhamPilot

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-UNTILT-TOPOLOGY
source: Joshi local untilt embeddings and III relative-degree normalization;
the same actual completion embedding and torsion-root de Rham pilot.
fidelity: proves the constructed torsion-completion embedding into the same
actual untilt is closed and continuous. Proves its norm power law on every
element, with the original relative ramification/inertia product retained.
No isometry or topological certificate is input. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology

open JoshiTeich.Prologue InitialThetaCanonicalGeometricFontaine InitialThetaTorsionDeRhamPilot
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (v : NumberField.FinitePlace ↥D.prime.torsionField)
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)

theorem embedding_isClosedEmbedding : Topology.IsClosedEmbedding (embedding D w v hvw) :=
  FiniteCompletionEmbeddingTopology.isClosedEmbedding hvw (completionEmbedding D w)
    (completionEmbedding_isometry D w).continuous

theorem embedding_continuous : Continuous (embedding D w v hvw) :=
  (embedding_isClosedEmbedding D w v hvw).continuous

theorem embedding_range_isClosed : IsClosed (Set.range (embedding D w v hvw)) :=
  (embedding_isClosedEmbedding D w v hvw).isClosed_range

theorem embedding_norm_lt_one_iff (x : LocalCompletion.completionAt ↥D.prime.torsionField v) :
    ‖embedding D w v hvw x‖ < 1 ↔ ‖x‖ < 1 :=
  ClosedFieldEmbeddingNorm.norm_lt_one_iff _ (embedding_isClosedEmbedding D w v hvw).isEmbedding x

theorem embedding_norm_pow (x : LocalCompletion.completionAt ↥D.prime.torsionField v) :
    ‖x‖ = ‖embedding D w v hvw x‖ ^
      (iutRelativeRamificationIndex (v := v) (w := w.1) * Arithmetic.relInertDeg v w.1) := by
  apply ClosedFieldEmbeddingNorm.norm_eq_pow _ (embedding_isClosedEmbedding D w v hvw).isEmbedding
    (iutEmbedCompletion hvw ((iutInitialThetaTateParameterData D).parameter w.1)) _
  · rw [embedding_base]
    exact InitialThetaTateDeRhamPilot.tateValue_ne_zero D w
  · rw [embedding_base]
    exact InitialThetaTateDeRhamPilot.tateValue_norm_lt_one D w
  · rw [iutEmbedCompletion_norm_eq_pow, embedding_base, completionEmbedding_norm]

theorem embedding_dist_pow (x y : LocalCompletion.completionAt ↥D.prime.torsionField v) :
    dist x y = dist (embedding D w v hvw x) (embedding D w v hvw y) ^
      (iutRelativeRamificationIndex (v := v) (w := w.1) * Arithmetic.relInertDeg v w.1) := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact embedding_norm_pow D w v hvw (x - y)

theorem embedding_log_norm (x : LocalCompletion.completionAt ↥D.prime.torsionField v) :
    Real.log ‖x‖ =
      ((iutRelativeRamificationIndex (v := v) (w := w.1) * Arithmetic.relInertDeg v w.1 : ℕ) : ℝ) *
        Real.log ‖embedding D w v hvw x‖ := by
  rw [embedding_norm_pow, Real.log_pow]

end
end JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology
