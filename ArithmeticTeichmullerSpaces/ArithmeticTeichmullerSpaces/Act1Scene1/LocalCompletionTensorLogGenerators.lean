import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarHullVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-ORDINARY-LOG-GENERATORS
source: actual normalized p-adic logarithm small-ball surjectivity and
Joshi III multiplicative log-shell picture (3474--3478).
fidelity: constructs pure tensors of scalar times normalized ordinary logs,
proves exact scalar generator coverage and computes their normalization
hull. It does not identify ordinary log values with Bloch-Kato theta classes.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open NumberField
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance tensorLogGeneratorCharZero (i : ι) : CharZero (P.Factor i) :=
  charZero_of_injective_ringHom (FinitePlace.embedding (P.place i).maximalIdeal).injective
local instance tensorLogGeneratorIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

private theorem norm_prime_lt_one (i : ι) : ‖(p : P.Factor i)‖ < 1 := by
  have h := norm_natCast_prime_lt_one (P.residueChar_eq i)
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

def logScalarGenerators (z : ∀ i, P.Factor i) : Set P.Tensor :=
  {t | ∃ b : ∀ i, P.Factor i, (∀ i, ‖b i‖ ≤ 1) ∧
    P.pure (fun i => z i * LocalPadicLog.normalizedLog p (b i)) = t}

theorem logScalarGenerators_eq_scalarGenerators (z : ∀ i, P.Factor i) :
    P.logScalarGenerators z = P.scalarGenerators z := by
  ext t
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨fun i => LocalPadicLog.normalizedLog p (b i), fun i => ?_, rfl⟩
    rw [LocalPadicLog.norm_normalizedLog (Fact.out : p.Prime) (norm_prime_lt_one P i) (hb i)]
    exact hb i
  · rintro ⟨a, ha, rfl⟩
    choose b hb heq using fun i => LocalPadicLog.exists_normalizedLog_eq
      (Fact.out : p.Prime) (norm_prime_lt_one P i) (ha i)
    exact ⟨b, hb, congrArg P.pure (funext fun i => congrArg (fun x => z i * x) (heq i))⟩

theorem integralHull_logScalarGenerators (z : ∀ i, P.Factor i) :
    P.integralHull (P.logScalarGenerators z) = P.scalarLattice z := by
  rw [P.logScalarGenerators_eq_scalarGenerators, P.integralHull_scalarGenerators]

theorem logScalarGenerators_subset_unitLattice (z : ∀ i, P.Factor i)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) : P.logScalarGenerators z ⊆ P.unitLattice := by
  rw [P.logScalarGenerators_eq_scalarGenerators]
  rintro _ ⟨a, ha, rfl⟩
  apply P.pure_mem_lattice
  intro i
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
  exact (mul_le_mul_of_nonneg_right (hz1 i) (norm_nonneg _)).trans (by simpa using ha i)

theorem normalizationHull_logScalarGenerators (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) :
    (P.normalizationHull (P.logScalarGenerators z) : Set P.Tensor) =
      (P.scalarNormalization z hz : Set P.Tensor) := by
  rw [← P.normalizationHull_integralHull (P.logScalarGenerators z),
    P.integralHull_logScalarGenerators,
    P.normalizationHull_eq_leastHull _ (P.scalarLattice_isCompact_of_nonzero z hz).isBounded
      (P.scalarLattice_normalizationHaar_pos z hz), P.leastHull_scalarLattice z hz]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
