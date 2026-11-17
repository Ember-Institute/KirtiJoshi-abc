/-
Adaptation provenance: exact accepted Iut AST command spans.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Tripod/CurveOf.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfGenerator
import Theorems.Thm_AbcAdaptation_Tripod_legendre_isElliptic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField
open scoped IntermediateField

theorem gen'_ne_zero {l : Qbar} (hl : l ≠ 0) : gen' l ≠ 0 := by
  intro h
  exact hl (congrArg Subtype.val h)

theorem gen'_ne_one {l : Qbar} (hl : l ≠ 1) : gen' l ≠ 1 := by
  intro h
  exact hl (congrArg Subtype.val h)

/-- `ℚ̄` is torsion-free over every intermediate field `F ⊆ ℚ̄` (an explicit instance, since
the generic search times out). -/
instance (F : IntermediateField ℚ Qbar) : Module.IsTorsionFree F Qbar :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap F Qbar).injective

/-- `ℚ̄` is an algebraic closure of every intermediate field `F ⊆ ℚ̄`. -/
instance (F : IntermediateField ℚ Qbar) : IsAlgClosure F Qbar := by
  haveI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  exact (isAlgClosure_iff F Qbar).mpr ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩

/-- The Legendre curve of `λ` over `F_λ` is elliptic. -/
theorem legendre_gen'_isElliptic (x : Pt) : (legendre (gen' x.1)).IsElliptic :=
  legendre_isElliptic (gen'_ne_zero x.2.1) (gen'_ne_one x.2.2)

end AbcAdaptation.Tripod
