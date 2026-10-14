import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndex

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-INTEGRAL-HULL
source: Joshi III pr:convexes-and-hulls (3597--3609), minimal integral
submodule hulls and collation; Mathlib integral spans.
fidelity: constructs the least Z_p-submodule of the actual tensor space
containing a set. A full nonzero scalar-generator family makes it open;
unit-lattice containment makes it compact. No decomposition into fields,
maximal order, paper holomorphic hull or untilt/Bloch-Kato identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance hullIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

def integralHull (U : Set P.Tensor) : Submodule ℤ_[p] P.Tensor :=
  Submodule.span ℤ_[p] U

def scalarGenerators (z : ∀ i, P.Factor i) : Set P.Tensor :=
  {t | ∃ a : ∀ i, P.Factor i, (∀ i, ‖a i‖ ≤ 1) ∧ P.pure (fun i => z i * a i) = t}

theorem integralHull_le_iff (U : Set P.Tensor) (L : Submodule ℤ_[p] P.Tensor) :
    P.integralHull U ≤ L ↔ U ⊆ L := Submodule.span_le

theorem integralHull_iUnion {κ : Type*} (U : κ → Set P.Tensor) :
    P.integralHull (⋃ k, U k) = ⨆ k, P.integralHull (U k) :=
  Submodule.span_iUnion U

theorem integralHull_scalarGenerators (z : ∀ i, P.Factor i) :
    P.integralHull (P.scalarGenerators z) = P.scalarLattice z := by
  unfold integralHull scalarGenerators scalarLattice lattice
  congr 1
  ext t
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun i => z i * a i,
      fun i => ⟨a i, by simpa only [Metric.mem_closedBall, dist_zero_right] using ha i, rfl⟩,
      rfl⟩
  · rintro ⟨b, hb, rfl⟩
    choose a ha heq using hb
    refine ⟨a, fun i => by simpa only [Metric.mem_closedBall, dist_zero_right] using ha i, ?_⟩
    exact congrArg P.pure (funext heq)

theorem scalarLattice_le_integralHull (U : Set P.Tensor) (z : ∀ i, P.Factor i)
    (hgen : P.scalarGenerators z ⊆ U) : P.scalarLattice z ≤ P.integralHull U := by
  rw [← P.integralHull_scalarGenerators z]
  exact Submodule.span_mono hgen

theorem integralHull_le_unitLattice (U : Set P.Tensor) (hU : U ⊆ P.unitLattice) :
    P.integralHull U ≤ P.unitLattice :=
  (P.integralHull_le_iff U P.unitLattice).mpr hU

theorem integralHull_isOpen (U : Set P.Tensor) (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) (hgen : P.scalarGenerators z ⊆ U) :
    IsOpen (P.integralHull U : Set P.Tensor) := by
  exact AddSubgroup.isOpen_of_mem_nhds (P.integralHull U).toAddSubgroup
    (Filter.mem_of_superset
      ((P.scalarLattice_isOpen z hz).mem_nhds (Submodule.zero_mem _))
      (P.scalarLattice_le_integralHull U z hgen))

theorem integralHull_isCompact (U : Set P.Tensor) (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) (hgen : P.scalarGenerators z ⊆ U) (hU : U ⊆ P.unitLattice) :
    IsCompact (P.integralHull U : Set P.Tensor) := by
  have hclosed := AddSubgroup.isClosed_of_isOpen (P.integralHull U).toAddSubgroup
    (P.integralHull_isOpen U z hz hgen)
  have hbound := P.unitLattice_isBounded.subset (P.integralHull_le_unitLattice U hU)
  exact hclosed.closure_eq ▸ hbound.isCompact_closure

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
