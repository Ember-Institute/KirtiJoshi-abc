import Lean
import Definitions.Def_FermatBelyiDifferentConductorChildren
import Definitions.Def_FermatRiemannComposition
import Definitions.Def_FermatFunctionDivisors
import Definitions.Def_FermatNoncriticalElementarySource
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; validation and source mappings are recorded with this unit.
-/

set_option autoImplicit false
open NumberField Module
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Source Heights/Different/NumberField.lean:53-74; proof-body reuse. -/
private theorem differentConductor_logDisc_tower
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] :
    Real.log |(discr L : ℝ)| / finrank ℚ L =
      Real.log |(discr F : ℝ)| / finrank ℚ F +
        Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / finrank ℚ L := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := F) (𝒪 := 𝓞 F) (L := L) (𝒪' := 𝓞 L)
  have hD : Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr differentIdeal_ne_bot
  have hF : (discr F).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero F)
  have hFL : (finrank F L : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  rw [← Int.cast_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ← Nat.cast_natAbs, h, Nat.cast_mul,
    Nat.cast_pow, Real.log_mul (by exact_mod_cast hD)
    (by positivity), Real.log_pow, ← finrank_mul_finrank ℚ F L, Nat.cast_mul, add_div,
    add_comm]
  congr 1
  rw [mul_comm ((finrank F L : ℕ) : ℝ), mul_div_mul_right _ _ hFL]

/-- The image field need not equal the full field. No degree equality is assumed. -/
theorem closedBelyiActualFieldDifferentTowerSource : BelyiActualFieldDifferentTower := by
  intro N M hRF φ x hgood
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
    (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
  simpa only [pointLogDiff, Tripod.logDiff, Tripod.deg_eq_finrank,
    belyiRelativeLogDifferent, QbarPoint.degree] using
    differentConductor_logDisc_tower (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf

end AbcAdaptation.Tripod.Fermat.Proper


open AbcAdaptation.Tripod.Fermat.Proper

theorem PlatformDirect0 : BelyiActualFieldDifferentTower := closedBelyiActualFieldDifferentTowerSource

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation; validation and source mappings are recorded with this unit.
-/

set_option autoImplicit false
open NumberField
open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

section
variable {F : Type*} [Field F] [NumberField F]
/-- Source Heights/Curve/Conductor.lean:43-74, unchanged proof body. -/
private theorem exists_one_lt_iff_tripod (w : FinitePlace F) {z : F} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (1 < w z ∨ 1 < w z⁻¹ ∨ 1 < w (1 - z)⁻¹) ↔ (w z ≠ 1 ∨ w (z - 1) ≠ 1) := by
  have hwz : 0 < w z := w.pos_iff.mpr hz0
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hwz1 : 0 < w (z - 1) := w.pos_iff.mpr hsub
  have hneg : w (1 - z) = w (z - 1) := by rw [← neg_sub, map_neg_eq_map]
  rw [map_inv₀, map_inv₀, hneg, one_lt_inv₀ hwz, one_lt_inv₀ hwz1]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h.ne'
    · exact Or.inl h.ne
    · exact Or.inr h.ne
  · rintro (h | h)
    · rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl h'
    · rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr (Or.inr h')
      · -- `|z − 1|_w > 1` forces `|z|_w > 1`
        left
        have hle : w (z - 1) ≤ max (w z) (w (-1 : F)) := by
          have := w.add_le z (-1)
          simpa [sub_eq_add_neg] using this
        rw [map_neg_eq_map, map_one] at hle
        rcases le_max_iff.mp hle with h1 | h1
        · linarith
        · linarith

end

theorem closedTripodGeneratorConductorIdentitySource : TripodGeneratorConductorIdentity := by
  intro y
  have hmeet (w : FinitePlace (Tripod.fieldOf y.1)) :
      (∃ a ∈ tripodConductorGenerators y, 1 < w a) ↔
        w (Tripod.gen y.1) ≠ 1 ∨ w (Tripod.gen y.1 - 1) ≠ 1 := by
    simpa [tripodConductorGenerators] using
      exists_one_lt_iff_tripod w (Tripod.gen_ne_zero y.2.1)
        (sub_ne_zero.mp (Tripod.gen_sub_one_ne_zero y.2.2))
  unfold Tripod.logCond finiteSetLogCond
  rw [Tripod.deg_eq_finrank]
  congr 1
  apply finsum_congr
  intro w
  simp only [Tripod.mem_badPlaces, hmeet w]

end AbcAdaptation.Tripod.Fermat.Proper


open AbcAdaptation.Tripod.Fermat.Proper

theorem PlatformDirect1 : TripodGeneratorConductorIdentity := closedTripodGeneratorConductorIdentitySource

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

theorem PlatformReduction : AbcAdaptation.Tripod.Fermat.Proper.BelyiDifferentConductorComparison := by
  exact AbcAdaptation.Tripod.Fermat.Proper.belyiDifferentConductorComparison_of_exact_children
    AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldConductorExtension
    AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldDifferentTower
    AbcAdaptation.Tripod.Fermat.Proper.tripodGeneratorConductorIdentity

open AbcAdaptation.Tripod.Fermat.Proper

theorem PlatformUploadType0 : BelyiActualFieldConductorExtension := AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldConductorExtension

theorem PlatformUploadType1 : BelyiActualFieldDifferentTower := AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldDifferentTower

theorem PlatformUploadType2 : TripodGeneratorConductorIdentity := AbcAdaptation.Tripod.Fermat.Proper.tripodGeneratorConductorIdentity

theorem PlatformOriginalParentType : AbcAdaptation.Tripod.Fermat.Proper.BelyiDifferentConductorComparison := PlatformReduction

theorem PlatformSourceParentType : BelyiDifferentConductorComparison := PlatformReduction

open Lean
run_meta do
  let pairs : Array (Name × Name × Bool) := #[(`AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldConductorExtension, `PlatformUploadType0, true),(`AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldDifferentTower, `PlatformUploadType1, false),(`AbcAdaptation.Tripod.Fermat.Proper.tripodGeneratorConductorIdentity, `PlatformUploadType2, false),(`AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldDifferentTower, `PlatformDirect0, false),(`AbcAdaptation.Tripod.Fermat.Proper.tripodGeneratorConductorIdentity, `PlatformDirect1, false),(`PlatformOriginalParentType, `PlatformReduction, true),(`PlatformSourceParentType, `PlatformReduction, true)]
  let mut rows : Array Json := #[]
  for (original, uploaded, expectedSorry) in pairs do
    let a ← getConstInfo original
    let c ← getConstInfo uploaded
    unless ← Meta.isDefEq a.type c.type do throwError "Exact uploaded/source type differs: {original}"
    let axs ← collectAxioms uploaded
    unless axs.contains `sorryAx == expectedSorry do throwError "Unexpected proof debt: {uploaded}"
    for ax in axs do
      unless (#[`propext, `Classical.choice, `Quot.sound].contains ax ||
          (expectedSorry && ax == `sorryAx)) do throwError "Unexpected axiom {ax}"
    rows := rows.push (Json.mkObj [("original",toJson original.toString),
      ("checked",toJson uploaded.toString),("type_equal",Json.bool true),
      ("expected_sorry",Json.bool expectedSorry),("axioms",toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/belyi-different-conductor-split-20261114/type-audit.json" (Json.pretty (Json.arr rows))
