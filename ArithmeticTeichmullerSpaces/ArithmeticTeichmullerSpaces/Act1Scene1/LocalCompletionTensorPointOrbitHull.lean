import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIndeterminacyRegion
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWitnessHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorHaarSubspaces

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-POINT-ORBIT-HULL
source: Joshi III principal hull (3568--3574), convex/hull comparison
(3597--3609); reference ThetaRegion.thetaFinite and Cor312/RightHandSide's
order: images, hull, then log-volume.
fidelity: finite point orbits and normalization-thickened orbits generate
exactly the same normalization module. For pure nonzero scalar tensors the
point hull is the existing least principal hull, with positive finite Haar.
The raw finite point orbit itself has zero Haar. No paper theta identification.
Original proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
open scoped Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance pointFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance pointFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance pointIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

/-- The finite orbit of the point, before multiplication by the normalization. -/
def factorPointOrbit (a : P.Tensor) : Set P.Tensor := P.factorIndeterminacyOrbit {a}

theorem mem_factorPointOrbit (a : P.Tensor) : a ∈ P.factorPointOrbit a :=
  P.subset_factorIndeterminacyOrbit {a} (Set.mem_singleton a)

theorem factorTensorAut_mem_factorPointOrbit (a : P.Tensor)
    (σ : ∀ i, P.Factor i ≃ₐ[ℚ_[p]] P.Factor i) :
    P.factorTensorAut σ a ∈ P.factorPointOrbit a :=
  Set.mem_iUnion₂.mpr ⟨_, ⟨σ, rfl⟩, ⟨a, Set.mem_singleton a, rfl⟩⟩

theorem factorPointOrbit_finite (a : P.Tensor) : (P.factorPointOrbit a).Finite :=
  P.factorIndeterminacies_finite.biUnion fun f _ => (Set.finite_singleton a).image f

theorem factorPointOrbit_isCompact (a : P.Tensor) : IsCompact (P.factorPointOrbit a) :=
  (P.factorPointOrbit_finite a).isCompact

theorem factorPointOrbit_subset_thickOrbit (a : P.Tensor) :
    P.factorPointOrbit a ⊆ P.factorIndeterminacyOrbit (P.principalRegion a) := by
  intro x hx
  obtain ⟨f, hf, y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  have hy' : y = a := Set.mem_singleton_iff.mp hy
  subst y
  exact Set.mem_iUnion₂.mpr ⟨f, hf, ⟨a, ⟨1, P.normalization.one_mem, mul_one a⟩, hxy⟩⟩

theorem thickOrbit_subset_normalizationHull_points (a : P.Tensor) :
    P.factorIndeterminacyOrbit (P.principalRegion a) ⊆
      (P.normalizationHull (P.factorPointOrbit a) : Set P.Tensor) := by
  intro x hx
  obtain ⟨f, hf, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨σ, rfl⟩ := hf
  obtain ⟨r, hr, rfl⟩ := hy
  have hr' : P.factorTensorAut σ r ∈ (P.normalization : Set P.Tensor) := by
    rw [← P.factorTensorAut_image_normalization σ]
    exact ⟨r, hr, rfl⟩
  have ha := P.subset_normalizationHull (P.factorPointOrbit a)
    (P.factorTensorAut_mem_factorPointOrbit a σ)
  have h := (P.normalizationHull (P.factorPointOrbit a)).smul_mem
    (⟨P.factorTensorAut σ r, hr'⟩ : P.normalization) ha
  change P.factorTensorAut σ r * P.factorTensorAut σ a ∈ P.normalizationHull _ at h
  rw [mul_comm] at h
  change P.factorTensorAut σ (a * r) ∈ P.normalizationHull (P.factorPointOrbit a)
  rw [map_mul]
  exact h

theorem normalizationHull_factorPointOrbit (a : P.Tensor) :
    P.normalizationHull (P.factorPointOrbit a) =
      P.normalizationHull (P.factorIndeterminacyOrbit (P.principalRegion a)) := by
  apply le_antisymm
  · exact Submodule.span_mono (P.factorPointOrbit_subset_thickOrbit a)
  · exact (P.normalizationHull_le_iff _ _).mpr (P.thickOrbit_subset_normalizationHull_points a)

theorem normalizationHull_pointOrbit_le_iff (a : P.Tensor) (b : P.Tensor) :
    (P.normalizationHull (P.factorPointOrbit a) : Set P.Tensor) ⊆ P.principalRegion b ↔
      P.factorPointOrbit a ⊆ P.principalRegion b :=
  P.normalizationHull_le_iff _ (P.principalNormalizationModule b)

theorem normalizationHull_purePointOrbit_eq_leastHull (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) :
    (P.normalizationHull (P.factorPointOrbit (P.pure z)) : Set P.Tensor) =
      P.leastHull (P.factorOrbitScalarRegion z hz)
        (P.factorOrbitScalarRegion_isCompact z hz).isBounded
        (P.factorOrbitScalarRegion_haar_pos_lt_top z hz).1 := by
  rw [P.normalizationHull_factorPointOrbit]
  have he : P.factorIndeterminacyOrbit (P.principalRegion (P.pure z)) =
      P.factorOrbitScalarRegion z hz := by
    rw [factorOrbitScalarRegion, P.scalarNormalization_eq_principalRegion]
  rw [he]
  exact P.normalizationHull_eq_leastHull _ _ _

theorem normalizationHull_purePointOrbit_haar_pos_lt_top (z : ∀ i, P.Factor i)
    (hz : ∀ i, z i ≠ 0) :
    0 < P.normalizationHaar (P.normalizationHull (P.factorPointOrbit (P.pure z))) ∧
      P.normalizationHaar (P.normalizationHull (P.factorPointOrbit (P.pure z))) < ⊤ := by
  rw [P.normalizationHull_purePointOrbit_eq_leastHull z hz]
  exact P.leastHull_haar_pos_lt_top _ _ _

/-- Singleton nullity follows from the already proved proper-subspace nullity. -/
theorem normalizationHaar_singleton_eq_zero (a : P.Tensor) : P.normalizationHaar {a} = 0 := by
  have : Nontrivial P.Tensor := Module.nontrivial_of_finrank_pos P.tensor_finrank_pos
  have hz : P.normalizationHaar ({0} : Set P.Tensor) = 0 := by
    have h := P.normalizationHaar_submodule_eq_zero (⊥ : Submodule ℚ_[p] P.Tensor) bot_ne_top
    simpa using h
  have he : (fun x : P.Tensor => a + x) ⁻¹' ({a} : Set P.Tensor) = {0} := by
    ext x
    simp
  rw [← measure_preimage_add P.normalizationHaar a {a}, he, hz]

theorem factorPointOrbit_haar_eq_zero (a : P.Tensor) :
    P.normalizationHaar (P.factorPointOrbit a) = 0 := by
  let : NullSingletonClass P.normalizationHaar := ⟨P.normalizationHaar_singleton_eq_zero⟩
  exact (P.factorPointOrbit_finite a).measure_zero P.normalizationHaar

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
