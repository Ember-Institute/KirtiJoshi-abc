import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorResidueMaximum
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorChosenHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIntegralHull

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-MODULE-HULL
source: Joshi III componentwise principal hull (3568--3574), compared with
the integral convex-closure discussion (3597--3609).
fidelity: proves the least principal hull of a bounded positive-Haar tensor
region is its span over the actual normalization. The proof uses attained
coordinate maxima and integral residue idempotents. It does not assume the
tensor integral order equals its normalization or identify paper theta loci.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance normalizationHullIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

def normalizationHull (U : Set P.Tensor) : Submodule P.normalization P.Tensor :=
  Submodule.span P.normalization U

omit [Fintype ι] in
theorem subset_normalizationHull (U : Set P.Tensor) : U ⊆ P.normalizationHull U :=
  Submodule.subset_span

omit [Fintype ι] in
theorem normalizationHull_le_iff (U : Set P.Tensor)
    (L : Submodule P.normalization P.Tensor) : P.normalizationHull U ≤ L ↔ U ⊆ L :=
  Submodule.span_le

theorem integralHull_subset_normalizationHull (U : Set P.Tensor) :
    (P.integralHull U : Set P.Tensor) ⊆ P.normalizationHull U := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact P.subset_normalizationHull U hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have h := (P.normalizationHull U).smul_mem (algebraMap ℤ_[p] P.normalization r) hx
    rw [Algebra.smul_def] at h
    change algebraMap ℤ_[p] P.Tensor r * x ∈ P.normalizationHull U at h
    rwa [← Algebra.smul_def r x] at h

theorem normalizationHull_integralHull (U : Set P.Tensor) :
    P.normalizationHull (P.integralHull U) = P.normalizationHull U := by
  apply le_antisymm
  · exact (P.normalizationHull_le_iff _ _).mpr (P.integralHull_subset_normalizationHull U)
  · exact Submodule.span_mono Submodule.subset_span

def principalNormalizationModule (a : P.Tensor) : Submodule P.normalization P.Tensor where
  carrier := P.principalRegion a
  zero_mem' := ⟨0, P.normalization.zero_mem, mul_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, P.normalization.add_mem hx hy, mul_add _ _ _⟩
  smul_mem' := by
    rintro r _ ⟨x, hx, rfl⟩
    refine ⟨(r : P.Tensor) * x, P.normalization.mul_mem r.2 hx, ?_⟩
    change a * ((r : P.Tensor) * x) = (r : P.Tensor) * (a * x)
    exact mul_left_comm _ _ _

theorem normalizationHull_subset_normalization (U : Set P.Tensor)
    (hU : U ⊆ P.normalization) : (P.normalizationHull U : Set P.Tensor) ⊆ P.normalization := by
  have h : P.normalizationHull U ≤ P.principalNormalizationModule 1 :=
    (P.normalizationHull_le_iff _ _).mpr fun x hx => ⟨x, hU hx, one_mul _⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h hx
  have hyx : y = x := by simpa only [one_mul] using hxy
  exact hyx ▸ hy

def residueIdempotent (I : MaximalSpectrum P.Tensor) : P.Tensor :=
  P.residueDecomposition.symm (Pi.single I 1)

theorem residueIdempotent_coordinate (I J : MaximalSpectrum P.Tensor) :
    Ideal.Quotient.mk J.asIdeal (P.residueIdempotent I) = if J = I then 1 else 0 := by
  change (P.residueDecomposition (P.residueDecomposition.symm (Pi.single I 1))) J = _
  rw [P.residueDecomposition.apply_symm_apply]
  by_cases h : J = I
  · subst J
    simp
  · simp [h]

theorem residueIdempotent_mem_normalization (I : MaximalSpectrum P.Tensor) :
    P.residueIdempotent I ∈ P.normalization := by
  rw [P.mem_normalization_iff_residueNorm_le_one]
  intro J
  rw [P.residueIdempotent_coordinate]
  split
  · rw [P.residueNorm_one]
  · rw [P.residueNorm_zero]; exact zero_le_one

theorem normalizationHull_eq_leastHull (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) :
    (P.normalizationHull U : Set P.Tensor) = P.leastHull U hU hpos := by
  letI : Fintype (MaximalSpectrum P.Tensor) := Fintype.ofFinite _
  choose x hx hx0 hxmax using fun I => P.exists_max_residueNorm U hU I
    (P.exists_residue_ne_zero_of_haar_pos hpos I)
  let a : P.Tensor := ∑ I : MaximalSpectrum P.Tensor, P.residueIdempotent I * x I
  have hcoords (J : MaximalSpectrum P.Tensor) :
      Ideal.Quotient.mk J.asIdeal a = Ideal.Quotient.mk J.asIdeal (x J) := by
    dsimp [a]
    rw [map_sum]
    simp only [map_mul, P.residueIdempotent_coordinate]
    simp
  have ha : IsUnit a := (P.isUnit_iff_residue_ne_zero a).mpr fun I => by
    rw [hcoords I]
    exact hx0 I
  have hUa : U ⊆ P.principalRegion a := fun y hy =>
    (P.mem_principalRegion_iff a ha y).mpr fun I => by
      rw [hcoords I]
      exact hxmax I y hy
  have haSpan : a ∈ P.normalizationHull U := by
    apply Submodule.sum_mem
    intro I _
    have h := (P.normalizationHull U).smul_mem
      (⟨P.residueIdempotent I, P.residueIdempotent_mem_normalization I⟩ : P.normalization)
      (P.subset_normalizationHull U (hx I))
    change P.residueIdempotent I * x I ∈ P.normalizationHull U at h
    exact h
  apply Set.Subset.antisymm
  · change P.normalizationHull U ≤ P.principalNormalizationModule (P.hullMultiplier U hU hpos)
    exact (P.normalizationHull_le_iff _ _).mpr (P.subset_leastHull U hU hpos)
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := P.leastHull_le_principalRegion U hU hpos a ha hUa hy
    have h := (P.normalizationHull U).smul_mem (⟨b, hb⟩ : P.normalization) haSpan
    change b * a ∈ P.normalizationHull U at h
    rwa [mul_comm] at h

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
