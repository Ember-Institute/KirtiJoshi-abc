import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHaar
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDegreeVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndex

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SCALAR-NORMALIZATION
source: actual tensor multiplication, integral closure, scalar determinant
Haar law; Joshi III scalar maximal-order hull shape (3568--3574).
fidelity: constructs z times the actual normalization, proves it is the
least normalization-module enlargement of the scalar tensor lattice, and
computes its normalization-Haar degree volume. This does not construct
least hulls for arbitrary subsets or identify paper norms/theta loci.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance saturationFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance saturationFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance saturationTensorFinite : Module.Finite ℚ_[p] P.Tensor :=
  Module.Finite.of_basis P.tensorBasis
local instance saturationIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])
variable (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)

theorem scale_eq_mul_pure (x : P.Tensor) : P.scale z hz x = P.pure z * x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    change P.scale z hz (r • P.pure a) = P.pure z * (r • P.pure a)
    rw [map_smul, P.scale_pure, mul_smul_comm, P.pure_mul]
  | add x y hx hy => rw [map_add, hx, hy, mul_add]

def scalarNormalization : Submodule ℤ_[p] P.Tensor :=
  P.normalization.toSubmodule.map (P.scaleIntegral z hz)

theorem scalarNormalization_eq_image :
    (P.scalarNormalization z hz : Set P.Tensor) =
      (P.continuousScale z hz) '' (P.normalization : Set P.Tensor) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩

theorem scalarLattice_le_scalarNormalization : P.scalarLattice z ≤ P.scalarNormalization z hz := by
  rw [← P.unitLattice_map_scale z hz]
  exact Submodule.map_mono P.unitLattice_le_normalization

private theorem pure_mem_scalarLattice : P.pure z ∈ P.scalarLattice z := by
  have h := P.pure_mem_lattice
    (fun i => (fun x : P.Factor i => z i * x) '' Metric.closedBall 0 1)
    z (fun i => ⟨1, by simp, mul_one _⟩)
  exact h

theorem scalarNormalization_mul_mem
    {a x : P.Tensor} (ha : a ∈ P.normalization) (hx : x ∈ P.scalarNormalization z hz) :
    a * x ∈ P.scalarNormalization z hz := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨a * y, P.normalization.mul_mem ha hy, ?_⟩
  change P.scale z hz (a * y) = a * P.scale z hz y
  rw [P.scale_eq_mul_pure, P.scale_eq_mul_pure]
  ring

theorem scalarNormalization_le_of_mul_closed (L : Submodule ℤ_[p] P.Tensor)
    (hL : ∀ a ∈ P.normalization, ∀ x ∈ L, a * x ∈ L)
    (hregion : P.scalarLattice z ≤ L) : P.scalarNormalization z hz ≤ L := by
  rintro _ ⟨y, hy, rfl⟩
  change P.scale z hz y ∈ L
  rw [P.scale_eq_mul_pure, mul_comm]
  exact hL y hy (P.pure z) (hregion (P.pure_mem_scalarLattice z))

theorem scalarNormalization_le_normalization (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    P.scalarNormalization z hz ≤ P.normalization.toSubmodule := by
  apply P.scalarNormalization_le_of_mul_closed z hz _
    (fun _ ha _ hx => P.normalization.mul_mem ha hx)
  exact (P.scalarLattice_le_unitLattice z hz1).trans P.unitLattice_le_normalization

theorem scalarNormalization_isCompact : IsCompact (P.scalarNormalization z hz : Set P.Tensor) := by
  rw [P.scalarNormalization_eq_image]
  exact P.normalization_isCompact.image (P.continuousScale z hz).continuous

theorem normalizationHaar_scalarNormalization_eq_det_norm :
    P.normalizationHaar (P.scalarNormalization z hz) = ENNReal.ofReal ‖P.scaleDet z hz‖ := by
  rw [P.scalarNormalization_eq_image,
    PadicHaar.measure_image_linearEquiv_eq_norm_det P.normalizationHaar (P.continuousScale z hz),
    P.normalizationHaar_normalization, mul_one]
  exact congrArg (fun x : ℚ_[p] => ENNReal.ofReal ‖x‖) (P.scaleMatrix_det_eq z hz).symm

def normalizationDegreeVolume (S : Set P.Tensor) : ℝ :=
  (P.normalizationHaar S).toReal ^ (1 / (Module.finrank ℚ_[p] P.Tensor : ℝ))

theorem normalizationDegreeVolume_scalarNormalization_eq_degreeVolume :
    P.normalizationDegreeVolume (P.scalarNormalization z hz) = P.degreeVolume (P.scalarLattice z) := by
  rw [normalizationDegreeVolume, degreeVolume,
    P.normalizationHaar_scalarNormalization_eq_det_norm,
    P.normalizedHaar_scalarLattice_eq_det_norm]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
