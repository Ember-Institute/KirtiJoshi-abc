/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean
-/
import Solutions.Source_TripodRelativeValuation
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_UniformizerSupply
import Mathlib.Topology.Algebra.UniformRing

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain WithZero

noncomputable section

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {v : FinitePlace K} {w : FinitePlace k}

private abbrev valuedBaseMap (v : FinitePlace K) (w : FinitePlace k) :
    WithVal (w.maximalIdeal.valuation k) →+* WithVal (v.maximalIdeal.valuation K) :=
  algebraMap _ _

private theorem continuous_valuedBaseMap (hvw : FinitePlace.LiesOver v w) :
    Continuous (valuedBaseMap v w) := by
  haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
  exact (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := k) (L := K)
    w.maximalIdeal v.maximalIdeal).continuous

private def embedValuedCompletion (hvw : FinitePlace.LiesOver v w) :
    (w.maximalIdeal.valuation k).Completion →+* (v.maximalIdeal.valuation K).Completion :=
  UniformSpace.Completion.mapRingHom (valuedBaseMap v w) (continuous_valuedBaseMap hvw)

private theorem valued_valuedBaseMap (hvw : FinitePlace.LiesOver v w)
    (x : WithVal (w.maximalIdeal.valuation k)) :
    Valued.v (valuedBaseMap v w x) = Valued.v x ^ Tripod.relRamIdx v w := by
  change v.maximalIdeal.valuation K (algebraMap k K x.ofVal) =
    w.maximalIdeal.valuation k x.ofVal ^ Tripod.relRamIdx v w
  exact Tripod.valuation_algebraMap_eq_pow hvw x.ofVal

private theorem valued_embedValuedCompletion (hvw : FinitePlace.LiesOver v w)
    (y : (w.maximalIdeal.valuation k).Completion) :
    Valued.v (embedValuedCompletion hvw y) = Valued.v y ^ Tripod.relRamIdx v w := by
  by_cases hy : y = 0
  · subst y
    simp [zero_pow (Tripod.relRamIdx_ne_zero hvw)]
  have hfy : embedValuedCompletion hvw y ≠ 0 := (map_ne_zero _).2 hy
  have h1 : {z | Valued.v z = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have hcont : Continuous (embedValuedCompletion hvw) :=
    UniformSpace.Completion.continuous_map
  have h2 : (embedValuedCompletion hvw) ⁻¹'
      {z | Valued.v z = Valued.v (embedValuedCompletion hvw y)} ∈ nhds y :=
    hcont.continuousAt.preimage_mem_nhds
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 hfy))
  obtain ⟨s, hsub, hs, hys⟩ := mem_nhds_iff.1 (Filter.inter_mem h1 h2)
  obtain ⟨x, hx⟩ := UniformSpace.Completion.denseRange_coe.exists_mem_open hs ⟨y, hys⟩
  obtain ⟨hx1, hx2⟩ := hsub hx
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx1 hx2
  rw [← hx1, ← hx2]
  rw [embedValuedCompletion, UniformSpace.Completion.mapRingHom_coe,
    Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
  exact valued_valuedBaseMap hvw x

/-- The extension of the field inclusion to completions at places with `v ∣ w`. -/
def embedCompletion (hvw : FinitePlace.LiesOver v w) :
    localCompletion w →+* localCompletion v :=
  (HeightOneSpectrum.adicCompletion.equiv K v.maximalIdeal).symm.toRingHom.comp
    ((embedValuedCompletion hvw).comp
      (HeightOneSpectrum.adicCompletion.equiv k w.maximalIdeal).toRingHom)

variable (hvw : FinitePlace.LiesOver v w)

/-- The comparison map extends the inclusion of the number fields. -/
theorem embedCompletion_embedding (x : k) :
    embedCompletion hvw (FinitePlace.embedding w.maximalIdeal x) =
      FinitePlace.embedding v.maximalIdeal (algebraMap k K x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  change embedValuedCompletion hvw
    (↑(WithVal.toVal (w.maximalIdeal.valuation k) x)) =
      (↑(WithVal.toVal (v.maximalIdeal.valuation K) (algebraMap k K x)))
  rw [embedValuedCompletion, UniformSpace.Completion.mapRingHom_coe]
  rfl

theorem continuous_embedCompletion : Continuous (embedCompletion hvw) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v.maximalIdeal).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion k w.maximalIdeal))

/-- The comparison map raises the discrete valuation to the relative ramification index. -/
theorem valued_embedCompletion (y : localCompletion w) :
    Valued.v (embedCompletion hvw y) = Valued.v y ^ Tripod.relRamIdx v w :=
  valued_embedValuedCompletion hvw y.toCompletion

/-- The comparison map preserves strict smallness in the adic norm. -/
theorem norm_embedCompletion_lt_one_iff (y : localCompletion w) :
    ‖embedCompletion hvw y‖ < 1 ↔ ‖y‖ < 1 := by
  rw [norm_lt_one_iff_valued, norm_lt_one_iff_valued, valued_embedCompletion]
  exact pow_lt_one_iff_of_nonneg zero_le (Tripod.relRamIdx_ne_zero hvw)

end

end AbcAdaptation.Reference.Iut
