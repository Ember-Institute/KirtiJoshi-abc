/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/LocalConstruct/Admissible.lean and
  Iut/Concrete/LocalConstruct/Hull.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalHaar
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorBoundedHull

/-!
# Admissible finite-place regions and least hulls

A region is admissible when it is nonempty, relatively compact, measurable,
and has positive finite Haar mass. For tuples over `p`, the actual completion
tensor theorem supplies the least unit-scaled integral region after transport
along the continuous algebra equivalence. When a factor has the wrong place,
the packet is the zero ring and its integral structure is the entire packet.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open MeasureTheory NumberField
open scoped Pointwise

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- The admissible regions of the finite-place packet. -/
def finiteAdmissible : Set (Set (Tensor K (.finite p) c)) :=
  {S | S.Nonempty ∧ IsCompact (closure S) ∧ MeasurableSet S ∧
    0 < finiteHaar p c S ∧ finiteHaar p c S < ⊤}

theorem finiteAdmissible_nonempty {U : Set (Tensor K (.finite p) c)}
    (hU : U ∈ finiteAdmissible p c) : U.Nonempty :=
  hU.1

theorem finiteAdmissible_relCompact {U : Set (Tensor K (.finite p) c)}
    (hU : U ∈ finiteAdmissible p c) : IsCompact (closure U) :=
  hU.2.1

theorem finiteAdmissible_smul_integral (a : Tensor K (.finite p) c) (ha : IsUnit a) :
    a • integral p c ∈ finiteAdmissible p c := by
  have hcompact := isCompact_smul_integral p c a
  exact ⟨⟨a • 1, Set.smul_mem_smul_set (one_mem_integral p c)⟩,
    hcompact.isClosed.closure_eq.symm ▸ hcompact,
    measurableSet_smul_integral p c a,
    finiteHaar_smul_integral_pos p c ha, finiteHaar_smul_integral_lt_top p c a⟩

theorem finiteAdmissible_integral : integral p c ∈ finiteAdmissible p c := by
  simpa only [one_smul] using finiteAdmissible_smul_integral p c 1 isUnit_one

theorem finiteComponentVol_prime_preimage_of_admissible (hc : ∀ j, IsOver K p (c j))
    {U : Set (Tensor K (.finite p) c)} (hU : U ∈ finiteAdmissible p c) :
    finiteComponentVol p c ((fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹' U) =
      finiteComponentVol p c U + Real.log (p : ℕ) :=
  finiteComponentVol_prime_preimage p c hc hU.2.2.1 hU.2.2.2.1 hU.2.2.2.2

private theorem genuineTensorEquiv_image_principalRegion (hc : ∀ j, IsOver K p (c j))
    (a : (genuinePacket p c hc).Tensor) :
    genuineTensorEquiv p c hc '' (genuinePacket p c hc).principalRegion a =
      genuineTensorEquiv p c hc a • integral p c := by
  rw [← genuineTensorEquiv_image_normalization p c hc]
  simp only [JoshiTeich.Act1Scene1.LocalCompletion.Packet.principalRegion, ← Set.image_smul,
    Set.image_image, smul_eq_mul, map_mul]

private theorem preimage_pos_of_addHaar_map {α G : Type*}
    [MeasurableSpace α] [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (f : α → G) (hf : Measurable f) (μ : Measure α) (ν : Measure G) [ν.IsAddHaarMeasure]
    (hmap : (μ.map f).IsAddHaarMeasure) {U : Set G} (hU : MeasurableSet U)
    (hpos : 0 < ν U) : 0 < μ (f ⁻¹' U) := by
  rw [← Measure.map_apply (μ := μ) hf hU]
  refine pos_iff_ne_zero.mpr ?_
  intro hzero
  rw [Measure.isAddLeftInvariant_eq_smul ν (μ.map f), Measure.smul_apply, hzero,
    smul_zero] at hpos
  exact (lt_irrefl _) hpos

/-- Pulling back a finite admissible region to the actual completion tensor preserves
positive Haar mass. -/
private theorem genuineTensorHaar_preimage_pos (hc : ∀ j, IsOver K p (c j))
    {U : Set (Tensor K (.finite p) c)} (hU : U ∈ finiteAdmissible p c) :
    0 < (genuinePacket p c hc).normalizationHaar
      (genuineTensorContinuousLinearEquiv p c hc ⁻¹' U) := by
  let e := genuineTensorContinuousLinearEquiv p c hc
  let μ := (genuinePacket p c hc).normalizationHaar
  change 0 < μ (e ⁻¹' U)
  have hmap : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  exact preimage_pos_of_addHaar_map e e.continuous.measurable μ (finiteHaar p c) hmap
    hU.2.2.1 hU.2.2.2.1

private theorem genuineTensor_preimage_isBounded (hc : ∀ j, IsOver K p (c j))
    {U : Set (Tensor K (.finite p) c)} (hU : IsCompact (closure U)) :
    Bornology.IsBounded (genuineTensorContinuousLinearEquiv p c hc ⁻¹' U) := by
  let e := (genuineTensorContinuousLinearEquiv p c hc).toHomeomorph
  change Bornology.IsBounded (e ⁻¹' U)
  exact (e.isCompact_preimage.mpr hU).isBounded.subset (Set.preimage_mono subset_closure)

private theorem genuineTensor_exists_least_preimage_hull (hc : ∀ j, IsOver K p (c j))
    {U : Set (Tensor K (.finite p) c)} (hU : U ∈ finiteAdmissible p c) :
    let P := genuinePacket p c hc
    let V := genuineTensorContinuousLinearEquiv p c hc ⁻¹' U
    ∃ a : P.Tensor, IsUnit a ∧ V ⊆ P.principalRegion a ∧
      ∀ b : P.Tensor, IsUnit b → V ⊆ P.principalRegion b →
        P.principalRegion a ⊆ P.principalRegion b := by
  have hpos := genuineTensorHaar_preimage_pos p c hc (U := U) hU
  have hcompact := finiteAdmissible_relCompact p c (U := U) hU
  have hbounded := genuineTensor_preimage_isBounded p c hc (U := U) hcompact
  obtain ⟨a, ha, hUa, -, -, -, hmin⟩ :=
    (genuinePacket p c hc).exists_least_positiveHaar_hull _ hbounded hpos
  exact ⟨a, ha, hUa, hmin⟩

/-- Every admissible finite region has a least unit-scaled integral region containing it. -/
theorem exists_leastHull_finite {U : Set (Tensor K (.finite p) c)}
    (hU : U ∈ finiteAdmissible p c) :
    ∃ a : Tensor K (.finite p) c, IsUnit a ∧ U ⊆ a • integral p c ∧
      ∀ b : Tensor K (.finite p) c, IsUnit b → U ⊆ b • integral p c →
        a • integral p c ⊆ b • integral p c := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · let P := genuinePacket p c hc
    let f := genuineTensorEquiv p c hc
    let V : Set P.Tensor := genuineTensorContinuousLinearEquiv p c hc ⁻¹' U
    obtain ⟨a, ha, hVa, hleast⟩ :=
      genuineTensor_exists_least_preimage_hull p c hc (U := U) hU
    have hVpreimage : V = f ⁻¹' U := rfl
    have hVimage : f '' V = U := by
      rw [hVpreimage]
      exact f.surjective.image_preimage U
    have hRegion (x : P.Tensor) : f '' P.principalRegion x = f x • integral p c :=
      genuineTensorEquiv_image_principalRegion p c hc x
    refine ⟨f a, ha.map f.toRingHom, ?_, ?_⟩
    · have h : f '' V ⊆ f '' P.principalRegion a := Set.image_mono hVa
      rwa [hVimage, hRegion a] at h
    · intro b hb hUb
      let b' := f.symm b
      have hb' : IsUnit b' := hb.map f.symm.toRingHom
      have hb_eq : f b' = b := f.apply_symm_apply b
      have hright : f '' P.principalRegion b' = b • integral p c := by
        rw [hRegion b', hb_eq]
      have hVb : V ⊆ P.principalRegion b' :=
        (Set.image_subset_image_iff f.injective).mp (by rwa [hVimage, hright])
      have h : f '' P.principalRegion a ⊆ f '' P.principalRegion b' :=
        Set.image_mono (hleast b' hb' hVb)
      rwa [hRegion a, hright] at h
  · obtain ⟨j, hj⟩ := not_forall.mp hc
    have := subsingleton_tensor_of_not_isOver p c j hj
    refine ⟨1, isUnit_one, ?_, ?_⟩
    · rw [one_smul, integral_eq_univ_of_subsingleton p c]
      exact Set.subset_univ _
    · intro b _ _
      have hb : b = 1 := Subsingleton.elim _ _
      exact hb.symm ▸ Set.Subset.rfl

end

end AbcAdaptation.Reference.Iut.LocalConstruct
