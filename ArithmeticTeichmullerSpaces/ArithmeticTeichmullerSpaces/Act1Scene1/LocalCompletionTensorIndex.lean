import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScale
import Mathlib.MeasureTheory.Group.Measure

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-INTEGRAL-INDEX
source: Joshi III `le:volume-lemma2/3`; compact integral tensor lattice
and Mathlib finite-coset Haar counting.
fidelity: computes normalized scalar-lattice Haar measure by its actual
finite additive index in the unit lattice. The factor-norm/degree formula
for that index and maximal-order/hull identification remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField MeasureTheory

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance indexFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance indexIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

instance unitLattice_compactSpace : CompactSpace P.unitLattice :=
  isCompact_iff_compactSpace.mp P.unitLatticeCompact.isCompact

theorem unitLattice_measurableEmbedding :
    MeasurableEmbedding ((↑) : P.unitLattice → P.Tensor) := by
  have h : IsClosed (P.unitLattice : Set P.Tensor) :=
    AddSubgroup.isClosed_of_isOpen P.unitLattice.toAddSubgroup
      (P.lattice_balls_isOpen (fun _ => 1) (fun _ => zero_lt_one))
  exact h.isClosedEmbedding_subtypeVal.measurableEmbedding

def unitHaar : Measure P.unitLattice :=
  P.normalizedHaar.comap ((↑) : P.unitLattice → P.Tensor)

instance unitHaar_isAddLeftInvariant : P.unitHaar.IsAddLeftInvariant :=
  Measure.IsAddLeftInvariant.comap P.normalizedHaar
    (f := P.unitLattice.subtype.toAddMonoidHom) P.unitLattice_measurableEmbedding

theorem unitHaar_univ : P.unitHaar Set.univ = 1 := by
  rw [unitHaar, P.unitLattice_measurableEmbedding.comap_apply,
    Set.image_univ, Subtype.range_coe_subtype]
  exact P.normalizedHaar_unitLattice

theorem scalarLattice_isOpen (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    IsOpen (P.scalarLattice z : Set P.Tensor) := by
  rw [← P.unitLattice_image_scale z hz]
  exact (P.continuousScale z hz).toHomeomorph.isOpenMap _
    (P.lattice_balls_isOpen (fun _ => 1) (fun _ => zero_lt_one))

theorem scalarLattice_isClosed (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    IsClosed (P.scalarLattice z : Set P.Tensor) :=
  AddSubgroup.isClosed_of_isOpen (P.scalarLattice z).toAddSubgroup (P.scalarLattice_isOpen z hz)

theorem scalarLattice_le_unitLattice (z : ∀ i, P.Factor i) (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    P.scalarLattice z ≤ P.unitLattice := by
  apply P.lattice_mono
  intro i
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hx).trans (hz1 i)

/-- The actual scalar tensor lattice, as a subgroup of the unit tensor lattice. -/
def scalarSubgroup (z : ∀ i, P.Factor i) : AddSubgroup P.unitLattice :=
  (P.scalarLattice z).toAddSubgroup.comap P.unitLattice.subtype.toAddMonoidHom

theorem scalarSubgroup_isOpen (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    IsOpen (P.scalarSubgroup z : Set P.unitLattice) :=
  (P.scalarLattice_isOpen z hz).preimage continuous_subtype_val

theorem scalarSubgroup_finiteIndex (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    (P.scalarSubgroup z).FiniteIndex := by
  letI := AddSubgroup.quotient_finite_of_isOpen (P.scalarSubgroup z) (P.scalarSubgroup_isOpen z hz)
  exact AddSubgroup.finiteIndex_of_finite_quotient

def scalarIndex (z : ∀ i, P.Factor i) : ℕ := (P.scalarSubgroup z).index

theorem scalarIndex_pos (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) : 0 < P.scalarIndex z := by
  letI := P.scalarSubgroup_finiteIndex z hz
  exact Nat.pos_of_ne_zero AddSubgroup.FiniteIndex.index_ne_zero

theorem scalarSubgroup_image (z : ∀ i, P.Factor i) (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    ((↑) : P.unitLattice → P.Tensor) '' (P.scalarSubgroup z : Set P.unitLattice) =
      P.scalarLattice z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, P.scalarLattice_le_unitLattice z hz1 hx⟩, hx, rfl⟩

theorem normalizedHaar_scalarLattice_eq_inv_index (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    P.normalizedHaar (P.scalarLattice z) = (P.scalarIndex z : ENNReal)⁻¹ := by
  letI := P.scalarSubgroup_finiteIndex z hz
  have hclosed : IsClosed (P.scalarSubgroup z : Set P.unitLattice) :=
    (P.scalarLattice_isClosed z hz).preimage continuous_subtype_val
  have h := AddSubgroup.index_mul_measure (P.scalarSubgroup z) hclosed.measurableSet P.unitHaar
  rw [P.unitHaar_univ] at h
  change (P.scalarIndex z : ENNReal) * P.unitHaar (P.scalarSubgroup z) = 1 at h
  rw [unitHaar, P.unitLattice_measurableEmbedding.comap_apply, P.scalarSubgroup_image z hz1] at h
  have h0 : (P.scalarIndex z : ENNReal) ≠ 0 := by exact_mod_cast (P.scalarIndex_pos z hz).ne'
  have htop : (P.scalarIndex z : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc
    _ = (P.scalarIndex z : ENNReal)⁻¹ *
        ((P.scalarIndex z : ENNReal) * P.normalizedHaar (P.scalarLattice z)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
    _ = (P.scalarIndex z : ENNReal)⁻¹ := by rw [h, mul_one]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
