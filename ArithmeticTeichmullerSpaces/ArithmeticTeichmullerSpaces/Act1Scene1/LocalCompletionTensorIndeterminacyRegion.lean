import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndeterminacy
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarHullVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-FACTOR-ORBIT-REGION
source: the finite factor-automorphism construction and actual scalar
normalization regions; reference `ThetaAdmissible.theta_admissible` and
`ThetaRegion.thetaFinite` supply the local container shape.
fidelity: constructs the finite union of images of an actual scaled
normalization, proves compactness and positive finite normalization Haar
measure, and proves containment in the normalization for integral scalars.
No admissibility, containment, or volume certificate is required from a caller.
This is a local container ingredient, not a paper theta-locus identification.
Original consumer proofs; no additional reference code copied.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance orbitRegionIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

def factorOrbitScalarRegion (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    Set P.Tensor :=
  P.factorIndeterminacyOrbit (P.scalarNormalization z hz)

theorem scalarNormalization_subset_factorOrbitScalarRegion
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    (P.scalarNormalization z hz : Set P.Tensor) ⊆ P.factorOrbitScalarRegion z hz :=
  P.subset_factorIndeterminacyOrbit _

theorem pure_mem_factorOrbitScalarRegion
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.pure z ∈ P.factorOrbitScalarRegion z hz := by
  apply P.scalarNormalization_subset_factorOrbitScalarRegion z hz
  refine ⟨1, P.normalization.one_mem, ?_⟩
  change P.scale z hz 1 = P.pure z
  rw [P.scale_eq_mul_pure, mul_one]

theorem factorOrbitScalarRegion_isCompact
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    IsCompact (P.factorOrbitScalarRegion z hz) :=
  P.factorIndeterminacyOrbit_isCompact (P.scalarNormalization_isCompact z hz)

theorem factorOrbitScalarRegion_haar_pos_lt_top
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    0 < P.normalizationHaar (P.factorOrbitScalarRegion z hz) ∧
      P.normalizationHaar (P.factorOrbitScalarRegion z hz) < ⊤ := by
  apply P.factorIndeterminacyOrbit_haar_pos_lt_top (P.scalarNormalization_isCompact z hz)
  exact (P.scalarLattice_normalizationHaar_pos z hz).trans_le
    (measure_mono (P.scalarLattice_le_scalarNormalization z hz))

theorem factorOrbitScalarRegion_subset_normalization
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    P.factorOrbitScalarRegion z hz ⊆ P.normalization := by
  intro x hx
  obtain ⟨φ, hφ, y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨σ, rfl⟩ := hφ
  rw [← P.factorTensorAut_image_normalization σ]
  exact ⟨y, P.scalarNormalization_le_normalization z hz hz1 hy, hxy⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
