import Definitions.Def_FermatBelyiConductorExtensionChildren
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldLocalConductorComparison
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentAccounting

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; see SOURCE_LEDGER.md.
-/

set_option autoImplicit false
open NumberField IsDedekindDomain Module
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper
namespace ConductorExtensionSource

section Meets

variable {K : Type*} [Field K] [NumberField K]

/-- The finite places at which some element of `G` has a pole: `{w | ∃ g ∈ G, 1 < w g}`. -/
def meets (G : Finset K) : Set (FinitePlace K) := {w | ∃ g ∈ G, 1 < w g}

/-- Only finitely many finite places meet a finite set. -/
theorem meets_finite (G : Finset K) : (meets G).Finite := by
  have h : meets G = ⋃ g ∈ G, {w : FinitePlace K | 1 < w g} := by
    ext w
    simp [meets]
  rw [h]
  refine Set.Finite.biUnion G.finite_toSet fun g _ => ?_
  by_cases hg : g = 0
  · subst hg
    refine Set.finite_empty.subset fun w (hw : 1 < w 0) => ?_
    rw [map_zero] at hw
    exact absurd hw (by norm_num)
  · refine (FinitePlace.hasFiniteMulSupport hg).subset fun w hw => ?_
    exact ne_of_gt hw

/-- `meets G` as a finset. -/
noncomputable def meetsFinset (G : Finset K) : Finset (FinitePlace K) := (meets_finite G).toFinset

lemma mem_meetsFinset {G : Finset K} {w : FinitePlace K} :
    w ∈ meetsFinset G ↔ ∃ g ∈ G, 1 < w g := by
  rw [meetsFinset, Set.Finite.mem_toFinset]
  rfl

/-- Convert the existing parent conductor definition, without a new conductor model. -/
theorem finiteSetLogCond_eq_sum (G : Finset K) :
    finiteSetLogCond G = (∑ w ∈ meetsFinset G, Real.log (placeNorm w)) / finrank ℚ K := by
  classical
  unfold finiteSetLogCond
  rw [finsum_eq_sum_of_support_subset _ (s := meetsFinset G)]
  · congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    simp only [if_pos (mem_meetsFinset.mp hw), placeNorm]
  · intro w hw
    rw [Function.mem_support] at hw
    rw [Finset.mem_coe, mem_meetsFinset]
    by_contra h
    exact hw (if_neg (by exact h))

end Meets

section Global

variable {F : Type*} [Field F] [NumberField F] {L : Type*} [Field L] [NumberField L]
  [Algebra F L]

/-- Source Conductor:149, now conditional on the exact grouped identity and finite support.
Nonnegativity of each actual ideal-multiplicity summand was proved in the carrier file. -/
theorem sum_diffContrib_le_of_accounting
    (hfinite : (Function.support fun 𝔭 : HeightOneSpectrum (𝓞 F) =>
      diffContrib L 𝔭.asIdeal).Finite)
    (haccount : Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L =
      ∑ᶠ 𝔭 : HeightOneSpectrum (𝓞 F), diffContrib L 𝔭.asIdeal)
    (U : Finset (FinitePlace F)) :
    ∑ u ∈ U, diffContrib L u.maximalIdeal.asIdeal ≤
      Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L := by
  classical
  have hinj : Set.InjOn (fun u : FinitePlace F => u.maximalIdeal) U :=
    fun _ _ _ _ h => (FinitePlace.maximalIdeal_inj _ _).mp h
  rw [← Finset.sum_image (g := fun u : FinitePlace F => u.maximalIdeal)
    (f := fun 𝔭 : HeightOneSpectrum (𝓞 F) => diffContrib L 𝔭.asIdeal) hinj, haccount]
  set s := U.image (fun u : FinitePlace F => u.maximalIdeal) ∪ hfinite.toFinset
  rw [finsum_eq_sum_of_support_subset _ (s := s)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun _ _ _ => diffContrib_nonneg _
  · intro 𝔭 h𝔭
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr h𝔭

/-- Source Conductor:170 finite combinatorics, with the arithmetic premises made explicit.
All finite element sets S,T and the algebra-map containment remain universally quantified. -/
theorem finiteSetLogCond_le_of_local_and_accounting
    (hlocal : ∀ u : FinitePlace F,
      Real.log (placeNorm u) / finrank ℚ F ≤
        (∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L) +
          diffContrib L u.maximalIdeal.asIdeal)
    (hfinite : (Function.support fun 𝔭 : HeightOneSpectrum (𝓞 F) =>
      diffContrib L 𝔭.asIdeal).Finite)
    (haccount : Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L =
      ∑ᶠ 𝔭 : HeightOneSpectrum (𝓞 F), diffContrib L 𝔭.asIdeal)
    (S : Finset F) (T : Finset L) (hST : S.image (algebraMap F L) ⊆ T) :
    finiteSetLogCond S ≤ finiteSetLogCond T +
      Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L := by
  classical
  set U := meetsFinset S
  set V := meetsFinset T
  have hdisj : Set.PairwiseDisjoint (U : Set (FinitePlace F)) (placesOver L) := by
    intro u₁ _ u₂ _ hne
    refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => hne ?_
    rw [eq_placeBelow (mem_placesOver.mp hw₁), eq_placeBelow (mem_placesOver.mp hw₂)]
  have hsub : U.biUnion (placesOver L) ⊆ V := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨a, ha, hua⟩ := mem_meetsFinset.mp hu
    refine mem_meetsFinset.mpr ⟨algebraMap F L a,
      hST (Finset.mem_image_of_mem _ ha), ?_⟩
    exact (one_lt_apply_algebraMap_iff (mem_placesOver.mp hwu) a).mpr hua
  rw [finiteSetLogCond_eq_sum, finiteSetLogCond_eq_sum, Finset.sum_div, Finset.sum_div]
  calc ∑ u ∈ U, Real.log (placeNorm u) / finrank ℚ F
      ≤ ∑ u ∈ U, ((∑ w ∈ placesOver L u,
          Real.log (placeNorm w) / finrank ℚ L) +
            diffContrib L u.maximalIdeal.asIdeal) :=
        Finset.sum_le_sum fun u _ => hlocal u
    _ = (∑ w ∈ U.biUnion (placesOver L), Real.log (placeNorm w) / finrank ℚ L) +
          ∑ u ∈ U, diffContrib L u.maximalIdeal.asIdeal := by
        rw [Finset.sum_add_distrib, Finset.sum_biUnion hdisj]
    _ ≤ _ := add_le_add
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
          div_nonneg (log_placeNorm_nonneg w) (by positivity))
        (sum_diffContrib_le_of_accounting hfinite haccount U)

end Global

end ConductorExtensionSource

/-- Complete conditional composer for the unchanged parent child. The algebra is explicitly
installed from the actual image-field inclusion, then the generic finite-place proof is applied. -/
theorem belyiActualFieldConductorExtension_of_local_and_accounting
    (hlocal : BelyiActualFieldLocalConductorComparison)
    (haccount : BelyiActualFieldDifferentAccounting) :
    BelyiActualFieldConductorExtension := by
  classical
  intro N M hRF φ x hgood
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
    (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
  intro S T hST
  have hl := hlocal M hRF φ x hgood
  obtain ⟨hf, ha⟩ := haccount M hRF φ x hgood
  have h := ConductorExtensionSource.finiteSetLogCond_le_of_local_and_accounting
    hl hf ha S T (by
      simpa only [Finset.image_subset_iff, RingHom.algebraMap_toAlgebra,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hST)
  simpa only [belyiRelativeLogDifferent, QbarPoint.degree] using h

end AbcAdaptation.Tripod.Fermat.Proper

open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

theorem solution : BelyiActualFieldConductorExtension :=
  AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldConductorExtension_of_local_and_accounting
    AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldLocalConductorComparison
    AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldDifferentAccounting
