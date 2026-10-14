import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIntegralHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarHullVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-HULL-ORDER-AUDIT
source: Joshi III pr:convexes-and-hulls (3597--3609), compared with the
principal maximal-order hull definition (3568--3574).
fidelity: proves the exact condition for the integral-module hull and the
principal normalization hull of a nonzero scalar tensor lattice to agree.
Their equality requires the tensor integral order to equal its normalization;
the normalization Haar enlargement factor is the actual normalization mass.
No particular packet with a proper integral order is assumed or constructed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance orderAuditIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

omit [Fintype ι] in
theorem integralHull_submodule (L : Submodule ℤ_[p] P.Tensor) :
    P.integralHull (L : Set P.Tensor) = L := Submodule.span_eq L

variable (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)

theorem scalarNormalization_eq_scalarLattice_iff :
    P.scalarNormalization z hz = P.scalarLattice z ↔
      P.normalization.toSubmodule = P.unitLattice := by
  rw [← P.unitLattice_map_scale z hz]
  change P.normalization.toSubmodule.map (P.scaleIntegral z hz) =
    P.unitLattice.map (P.scaleIntegral z hz) ↔ _
  exact (Submodule.map_injective_of_injective
    (show Function.Injective (P.scaleIntegral z hz) from (P.scale z hz).injective)).eq_iff

include hz in
theorem leastHull_scalarLattice_eq_integralHull_iff
    (hU : Bornology.IsBounded (P.scalarLattice z : Set P.Tensor))
    (hpos : 0 < P.normalizationHaar (P.scalarLattice z)) :
    P.leastHull (P.scalarLattice z) hU hpos =
        (P.integralHull (P.scalarLattice z) : Set P.Tensor) ↔
      P.normalization.toSubmodule = P.unitLattice := by
  rw [P.integralHull_submodule, P.leastHull_scalarLattice z hz]
  exact SetLike.coe_injective.eq_iff.trans (P.scalarNormalization_eq_scalarLattice_iff z hz)

theorem normalizationMass_eq_one_iff :
    P.normalizationMass = 1 ↔ P.normalization.toSubmodule = P.unitLattice := by
  constructor
  · intro hmass
    apply le_antisymm _ P.unitLattice_le_normalization
    intro x hx
    by_contra hxnot
    have hpos : 0 < P.normalizedHaar
        ((P.normalization : Set P.Tensor) \ (P.unitLattice : Set P.Tensor)) :=
      (P.normalization_isOpen.sdiff P.unitLatticeCompact.isCompact.isClosed).measure_pos _
        ⟨x, hx, hxnot⟩
    have hzero : P.normalizedHaar
        ((P.normalization : Set P.Tensor) \ (P.unitLattice : Set P.Tensor)) = 0 := by
      have hsub : (P.unitLattice : Set P.Tensor) ⊆ (P.normalization : Set P.Tensor) :=
        fun _ hx => P.unitLattice_le_normalization hx
      rw [measure_sdiff hsub
        P.unitLatticeCompact.isCompact.isClosed.measurableSet.nullMeasurableSet
        (by rw [P.normalizedHaar_unitLattice]; exact ENNReal.one_ne_top)]
      change P.normalizationMass - P.normalizedHaar P.unitLattice = 0
      rw [hmass, P.normalizedHaar_unitLattice, tsub_self]
    exact hpos.ne' hzero
  · intro heq
    have hset : (P.normalization : Set P.Tensor) = (P.unitLattice : Set P.Tensor) :=
      Set.Subset.antisymm heq.le heq.ge
    change P.normalizedHaar (P.normalization : Set P.Tensor) = 1
    rw [hset]
    exact P.normalizedHaar_unitLattice

theorem normalizationHaar_scalarNormalization_eq_mass_mul_scalarLattice :
    P.normalizationHaar (P.scalarNormalization z hz) =
      P.normalizationMass * P.normalizationHaar (P.scalarLattice z) := by
  rw [← P.normalizedHaar_eq_normalizationMass_mul,
    P.normalizationHaar_scalarNormalization_eq_det_norm,
    P.normalizedHaar_scalarLattice_eq_det_norm]

include hz in
theorem leastHull_scalarLattice_ne_integralHull_of_order_ne
    (hU : Bornology.IsBounded (P.scalarLattice z : Set P.Tensor))
    (hpos : 0 < P.normalizationHaar (P.scalarLattice z))
    (hne : P.normalization.toSubmodule ≠ P.unitLattice) :
    P.leastHull (P.scalarLattice z) hU hpos ≠
      (P.integralHull (P.scalarLattice z) : Set P.Tensor) :=
  fun h => hne ((P.leastHull_scalarLattice_eq_integralHull_iff z hz hU hpos).mp h)

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
