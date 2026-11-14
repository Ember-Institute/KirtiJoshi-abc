import Definitions.Def_FermatRiemannComposition
import Definitions.Def_FermatFunctionDivisors
import Definitions.Def_FermatBelyiDifferentConductorChildren
import Definitions.Def_FermatNoncriticalElementarySource
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors; The genl contributors

Independent source-proof adaptation of Belyi/CurveField/CoordRing.lean:38-163
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: d21848a412ff4da577615f237816c973cbe3dfd0790f0123f8ff3bc5b11eb180.
The original source's finite place set is the support of the actual existing
Divisor M. The existing coordRing and CuspGenerators are preserved exactly.
The cusp specialization also adapts Genl/Curves/BelyiDescent.lean:289-304
at ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf.
Source SHA-256: fab56e0073e8ad10a1cea54552ba10a62df5cef54da2f572136975cffe375596.
This module contains substantial source proofs; it belongs to the local
Solutions/Source layer and is not a platform Definition submission.
See source-consumer.json for source spans and actual consumers.
-/

set_option autoImplicit false
open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper.CuspCoordRingSource

variable {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
variable [IsCurveField M.K]









/-- The existing reduced cusp divisor has exactly its stated coefficients. -/
theorem cuspDivisor_apply (φ : M.K) (hfin : (cusps M hDVR φ).Finite)
    (P : Place M.K) :
    cuspDivisor M hDVR φ hfin P = if P ∈ cusps M hDVR φ then 1 else 0 := by
  classical
  rw [cuspDivisor, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [Set.Finite.mem_toFinset]







end AbcAdaptation.Tripod.Fermat.Proper.CuspCoordRingSource

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors; The genl contributors

Independent source adaptation; validation and source mappings are recorded with this unit.
-/

set_option autoImplicit false
open NumberField
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- Reuse the already proved cusp-value equivalence, not a new geometric child. -/
theorem differentConductor_notMem_cusps (M : Model N) (hDVR : PlacesDiscrete M)
    (φ : M.K) (hB : IsBelyi M hDVR φ) (x : QbarPoint M.K)
    (hgood : GoodValue M x φ) : x.P ∉ cusps M hDVR φ := by
  obtain ⟨hφ, h0, h1⟩ := hgood
  rw [noncritical_cusp_value_iff M hDVR φ hB.1 x]
  simp only [noncriticalValue, dif_pos hφ, NoncriticalP1.mem_zeroOneInf,
    Option.some.injEq, reduceCtorEq, false_or]
  exact not_or.mpr ⟨h0, h1⟩

/-- Every generator of the specified coordinate ring is regular, including generators
beyond the three distinguished tripod functions. -/
theorem differentConductor_generators_regular (M : Model N) (hDVR : PlacesDiscrete M)
    (φ : M.K) (hB : IsBelyi M hDVR φ) (hfin : (cusps M hDVR φ).Finite)
    (G : CuspGenerators M hDVR φ hfin) (x : QbarPoint M.K)
    (hgood : GoodValue M x φ) : ∀ g ∈ G.G, g ∈ x.P.1 := by
  letI : IsCurveField M.K := M.isCurveField
  intro g hg
  have hmem : g ∈ coordRing M (cuspDivisor M hDVR φ hfin) := by
    rw [← G.generate]
    exact Algebra.subset_adjoin hg
  apply hmem x.P
  rw [CuspCoordRingSource.cuspDivisor_apply M hDVR φ hfin x.P,
    if_neg (differentConductor_notMem_cusps M hDVR φ hB x hgood)]

/-- Expand the actual regular-generator conductor. -/
theorem differentConductor_logCondOf_eq (M : Model N) (hRF : ResiduesFinite M)
    (x : QbarPoint M.K) (G : Finset M.K) (hG : ∀ g ∈ G, g ∈ x.P.1) :
    letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
    logCondOf M hRF G x = finiteSetLogCond (evaluatedCuspGenerators x G hG) := by
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  unfold logCondOf
  rw [dif_pos hG]
  unfold finiteSetLogCond evaluatedCuspGenerators QbarPoint.degree
  congr 1
  apply finsum_congr
  intro w
  have hmeet : (∃ (g : M.K) (hg : g ∈ G),
      1 < w (evalInPointField x g (hG g hg))) ↔
      ∃ a ∈ G.attach.image (fun g => evalInPointField x g.1 (hG g.1 g.2)),
        1 < w a := by
    constructor
    · rintro ⟨g, hg, hw⟩
      exact ⟨evalInPointField x g (hG g hg),
        Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩, hw⟩
    · rintro ⟨a, ha, hw⟩
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨g.1, g.2, hw⟩
  simp only [hmeet]

/-- Actual evaluation of all three functions commutes with the image-field inclusion. -/
theorem differentConductor_generator_image_subset (M : Model N) (φ : M.K)
    (x : QbarPoint M.K) (hgood : GoodValue M x φ) (G : Finset M.K)
    (hG : ∀ g ∈ G, g ∈ x.P.1)
    (hφG : φ ∈ G) (hiG : φ⁻¹ ∈ G) (h1G : (1 - φ)⁻¹ ∈ G) :
    (tripodConductorGenerators (belyiImage M φ x)).image
      (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)) ⊆
      evaluatedCuspGenerators x G hG := by
  obtain ⟨hφ, h0, h1⟩ := hgood
  have hval : (belyiImage M φ x).1 = x.eval φ hφ :=
    congrArg Subtype.val (belyiImage_eq M φ x hφ h0 h1)
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  simp only [tripodConductorGenerators, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · apply Finset.mem_image.mpr
    refine ⟨⟨φ, hφG⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    simpa only [evalInPointField, IntermediateField.coe_inclusion, Tripod.coe_gen] using hval.symm
  · apply Finset.mem_image.mpr
    refine ⟨⟨φ⁻¹, hiG⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    change x.eval φ⁻¹ (hG _ hiG) = ((Tripod.gen (belyiImage M φ x).1)⁻¹ : Qbar)
    rw [x.noncritical_eval_inv hφ (hG _ hiG)]
    simp only [map_inv₀, Tripod.coe_gen, hval]
  · apply Finset.mem_image.mpr
    refine ⟨⟨(1 - φ)⁻¹, h1G⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    change x.eval (1 - φ)⁻¹ (hG _ h1G) =
      ((1 - Tripod.gen (belyiImage M φ x).1)⁻¹ : Qbar)
    rw [x.noncritical_eval_inv (sub_mem x.P.1.one_mem hφ) (hG _ h1G),
      x.noncritical_eval_sub x.P.1.one_mem hφ, x.noncritical_eval_one]
    simp only [map_inv₀, map_sub, map_one, Tripod.coe_gen, hval]

/-- Equality of full fields is already part of the exact affine identification. -/
theorem differentConductor_pointLogDiff_affine (M : Model N) (hRF : ResiduesFinite M)
    (A : AffineIdentification M) (p : Fermat.Pt N) :
    pointLogDiff M hRF (affineLift M A p) = Fermat.logDiff p := by
  letI : FiniteDimensional ℚ (affineLift M A p).fieldOf :=
    pointField_finiteDimensional M hRF (affineLift M A p)
  have hdisc := NumberField.discr_eq_discr_of_algEquiv (affineLift M A p).fieldOf
    (IntermediateField.equivOfEq (affineLift_field_eq M A p))
  unfold pointLogDiff Fermat.logDiff
  rw [hdisc, affineLift_degree_eq]

/-- Complete conditional composer; the exact original conclusion is retained. -/
theorem belyiDifferentConductorComparison_of_exact_children
    (hExtension : BelyiActualFieldConductorExtension)
    (hTower : BelyiActualFieldDifferentTower)
    (hTripod : TripodGeneratorConductorIdentity) :
    BelyiDifferentConductorComparison := by
  intro N M hDVR hRF A φ hB hfin G
  refine ⟨0, fun p hgood => ?_⟩
  let x := affineLift M A p
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  have hG := differentConductor_generators_regular M hDVR φ hB hfin G x hgood
  have hsub := differentConductor_generator_image_subset M φ x hgood G.G hG
    G.phi_mem G.inv_phi_mem G.inv_one_sub_phi_mem
  have he := hExtension M hRF φ x hgood
    (tripodConductorGenerators (belyiImage M φ x))
    (evaluatedCuspGenerators x G.G hG) hsub
  have ht := hTower M hRF φ x hgood
  rw [← hTripod, ← differentConductor_logCondOf_eq M hRF x G.G hG] at he
  have hdiff : pointLogDiff M hRF x = Fermat.logDiff p :=
    differentConductor_pointLogDiff_affine M hRF A p
  change Tripod.logDiff (belyiImage M φ x) + Tripod.logCond (belyiImage M φ x) ≤
    Fermat.logDiff p + logCondOf M hRF G.G x + 0
  linarith

end AbcAdaptation.Tripod.Fermat.Proper

open AbcAdaptation.Tripod.Fermat.Proper

theorem solution : AbcAdaptation.Tripod.Fermat.Proper.BelyiDifferentConductorComparison := by
  exact AbcAdaptation.Tripod.Fermat.Proper.belyiDifferentConductorComparison_of_exact_children
    AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldConductorExtension
    AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldDifferentTower
    AbcAdaptation.Tripod.Fermat.Proper.tripodGeneratorConductorIdentity
