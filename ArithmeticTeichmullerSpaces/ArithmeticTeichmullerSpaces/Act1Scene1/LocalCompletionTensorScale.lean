import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorTopology
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SCALAR-IMAGE
source: Joshi III `le:volume-lemma2/3`, scalar integral tensor lattices;
Mathlib tensor congruence, finite-dimensional topology and Haar character.
fidelity: constructs the tensor automorphism of nonzero factor scalars,
identifies its image of the unit lattice, and computes the unit-lattice
normalized Haar measure as its Haar character. The character's numerical
factor-norm formula and maximal-order/hull identification remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField MeasureTheory TopologicalSpace
open scoped TensorProduct BigOperators Pointwise

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance scaleFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance scaleFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance scaleIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

def factorScale (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (i : ι) :
    P.Factor i ≃ₗ[ℚ_[p]] P.Factor i where
  toFun x := z i * x
  invFun x := (z i)⁻¹ * x
  left_inv x := inv_mul_cancel_left₀ (hz i) x
  right_inv x := mul_inv_cancel_left₀ (hz i) x
  map_add' x y := mul_add _ _ _
  map_smul' r x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    ring

def scale (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) : P.Tensor ≃ₗ[ℚ_[p]] P.Tensor :=
  PiTensorProduct.congr (P.factorScale z hz)

theorem scale_pure (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (a : ∀ i, P.Factor i) :
    P.scale z hz (P.pure a) = P.pure (fun i => z i * a i) :=
  PiTensorProduct.congr_tprod _ _

def scaleIntegral (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) : P.Tensor →ₗ[ℤ_[p]] P.Tensor where
  toFun := P.scale z hz
  map_add' := (P.scale z hz).map_add
  map_smul' r x := by
    change P.scale z hz ((r : ℚ_[p]) • x) = (r : ℚ_[p]) • P.scale z hz x
    exact (P.scale z hz).map_smul _ _

def scalarLattice (z : ∀ i, P.Factor i) : Submodule ℤ_[p] P.Tensor :=
  P.lattice (fun i => (fun x : P.Factor i => z i * x) '' Metric.closedBall 0 1)

theorem unitLattice_map_scale (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.unitLattice.map (P.scaleIntegral z hz) = P.scalarLattice z := by
  classical
  unfold unitLattice scalarLattice lattice
  rw [Submodule.map_span]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨fun i => z i * a i, fun i => ⟨a i, ha i, rfl⟩, (P.scale_pure z hz a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    choose b hb heq using ha
    refine ⟨P.pure b, ⟨b, hb, rfl⟩, ?_⟩
    change P.scale z hz (P.pure b) = P.pure a
    rw [P.scale_pure]
    exact congrArg P.pure (funext heq)

theorem unitLattice_image_scale (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    (P.scale z hz) '' (P.unitLattice : Set P.Tensor) = P.scalarLattice z := by
  rw [← P.unitLattice_map_scale z hz]
  rw [Submodule.map_coe]
  rfl

def continuousScale (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) : P.Tensor ≃L[ℚ_[p]] P.Tensor :=
  (P.scale z hz).toContinuousLinearEquiv

instance tensorAutomorphismAction : DistribMulAction (P.Tensor ≃L[ℚ_[p]] P.Tensor) P.Tensor where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero f := f.map_zero
  smul_add f := f.map_add

instance tensorAutomorphismContinuous : ContinuousConstSMul (P.Tensor ≃L[ℚ_[p]] P.Tensor) P.Tensor :=
  ⟨fun f => f.continuous⟩

def unitLatticeCompact : PositiveCompacts P.Tensor where
  carrier := P.unitLattice
  isCompact' := P.lattice_balls_isCompact (fun _ => 1) (fun _ => zero_lt_one) (fun _ => le_rfl)
  interior_nonempty' := by
    unfold unitLattice
    rw [(P.lattice_balls_isOpen (fun _ => 1) (fun _ => zero_lt_one)).interior_eq]
    exact ⟨0, Submodule.zero_mem _⟩

/-- Haar normalization is fixed by the actual tensor integral order. -/
def normalizedHaar : Measure P.Tensor := Measure.addHaarMeasure P.unitLatticeCompact
instance normalizedHaar_isAddHaarMeasure : P.normalizedHaar.IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure P.unitLatticeCompact).IsAddHaarMeasure
instance normalizedHaar_regular : P.normalizedHaar.Regular :=
  inferInstanceAs (Measure.addHaarMeasure P.unitLatticeCompact).Regular

theorem normalizedHaar_unitLattice : P.normalizedHaar P.unitLattice = 1 :=
  Measure.addHaarMeasure_self

theorem normalizedHaar_scalarLattice (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.normalizedHaar (P.scalarLattice z) =
      (distribHaarChar P.Tensor (P.continuousScale z hz) : ENNReal) := by
  have h := distribHaarChar_mul P.normalizedHaar (P.continuousScale z hz)
    (P.unitLattice : Set P.Tensor)
  rw [P.normalizedHaar_unitLattice, mul_one] at h
  change (distribHaarChar P.Tensor (P.continuousScale z hz) : ENNReal) =
    P.normalizedHaar ((P.scale z hz) '' (P.unitLattice : Set P.Tensor)) at h
  rw [P.unitLattice_image_scale] at h
  exact h.symm

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
