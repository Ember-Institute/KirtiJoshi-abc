/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/Core.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_JTransport
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut Polynomial

private noncomputable def jPolyRat (c : ℚ) : Polynomial Qbar :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C (c : Qbar) * (X ^ 2 * (X - 1) ^ 2)

private theorem jPolyRat_ne_zero (c : ℚ) : jPolyRat c ≠ 0 := by
  intro h
  have he : (jPolyRat c).eval 0 = 256 := by simp [jPolyRat]
  rw [h, eval_zero] at he
  exact absurd he (by norm_num)

private theorem isRoot_jPolyRat_of_legendreJ_eq (x : Pt) (c : ℚ)
    (hj : legendreJ x.1 = (c : Qbar)) : (jPolyRat c).IsRoot x.1 := by
  have hden : x.1 ^ 2 * (x.1 - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ x.2.1) (pow_ne_zero _ (sub_ne_zero.mpr x.2.2))
  rw [legendreJ, div_eq_iff hden] at hj
  rw [IsRoot, jPolyRat]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rw [hj, sub_self]

/-- Only finitely many tripod points have a Legendre `j`-invariant in a given finite rational set. -/
theorem finite_legendreJ_preimage (excJ : Finset ℚ) :
    {x : Pt | ∃ c ∈ excJ, legendreJ x.1 = (c : Qbar)}.Finite := by
  have hroots : (⋃ c ∈ (excJ : Set ℚ), {l : Qbar | (jPolyRat c).IsRoot l}).Finite :=
    excJ.finite_toSet.biUnion fun c _ => finite_setOfPred_isRoot (jPolyRat_ne_zero c)
  have hinj : Function.Injective (fun x : Pt => x.1) := Subtype.val_injective
  refine (hroots.preimage hinj.injOn).subset ?_
  rintro x ⟨c, hc, hj⟩
  exact Set.mem_iUnion₂.mpr ⟨c, hc, isRoot_jPolyRat_of_legendreJ_eq x c hj⟩

/-- The exceptional `j`-locus is finite for the curves supplied by `P`. -/
theorem finite_curve_j_preimage (P : CurveProviders) (excJ : Finset ℚ) :
    {x : Pt | ∃ c ∈ excJ, (P.curve x).E.j = (c : (P.curve x).F)}.Finite := by
  refine (finite_legendreJ_preimage excJ).subset ?_
  rintro x ⟨c, hc, hj⟩
  let f : (P.curve x).F →+* Qbar := algebraMap (fieldOf' x.1) Qbar
  have hgen : f (genC' P x) = x.1 := rfl
  rw [curve_j_eq_legendreJ P x] at hj
  have hmap := congrArg f hj
  rw [map_legendreJ f, hgen, map_ratCast f] at hmap
  exact ⟨c, hc, hmap⟩

/-- An exceptional `j`-locus containing all core failures gives the required finite set. -/
theorem coreFiniteness_of_exceptionalJ (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (AG : AnabelianGeometry.{0}) (excJ : Finset ℚ)
    (hCore :
      {x : Pt | ¬ OrbicurveDataSection.HasCoreUniversally AG (P.curve x).F (P.curve x).E} ⊆
        {x : Pt | ∃ c ∈ excJ, (P.curve x).E.j = (c : (P.curve x).F)}) :
    CoreFinitenessHyp P K d AG := by
  refine (finite_curve_j_preimage P excJ).subset ?_
  rintro x ⟨_, hx⟩
  exact hCore hx

end AbcAdaptation.Tripod
