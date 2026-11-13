/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent adaptation of Belyi/CurveField/Residue.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8. The existing proper residue field
and rational embedding are reused without a second carrier.
-/
import Definitions.Def_FermatCurveFieldPlace
import Mathlib.RingTheory.Jacobson.Ring

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

namespace Place

open IsLocalRing

variable {K : Type*} [Field K] [CharZero K] (P : Place K)

theorem residue_surjective : Function.Surjective P.residue :=
  IsLocalRing.residue_surjective

theorem residue_eq_zero_iff {a : P.1} :
    P.residue a = 0 ↔ a ∈ maximalIdeal P.1 :=
  IsLocalRing.residue_eq_zero_iff a

variable [IsCurveField K]

/-- Source proof: a chart residue is a surjective image of a finite type
ℚ-algebra. Zariski's lemma then makes this actual residue field finite. -/
instance curveField_finiteDimensional : FiniteDimensional ℚ P.ResidueField := by
  obtain ⟨t, ht, htP⟩ := P.exists_transcendental_mem
  have : Fact (Transcendental ℚ t) := ⟨ht⟩
  let φ : chartRing t →+* P.ResidueField := (IsLocalRing.residue P.1).comp
    ((algebraMap (chartRing t) K).codRestrict P.1 (P.algebraMap_chartRing_mem t htP))
  have hφ : Function.Surjective φ := P.residue_comp_surjective t htP
  have : Algebra.FiniteType ℚ P.ResidueField :=
    Algebra.FiniteType.of_surjective φ.toRatAlgHom hφ
  exact finite_of_finite_type_of_isJacobsonRing ℚ P.ResidueField

theorem degree_pos : 0 < P.degree := Module.finrank_pos

end Place

/-- The fixed model supplies the sole field of the source curve-field class.
The source Dedekind chart proof then gives the existing geometric child. -/
theorem model_placesDiscrete {N : ℕ} (M : Model N) : PlacesDiscrete M := by
  letI : IsCurveField M.K := M.isCurveField
  intro P
  infer_instance

/-- The same source class closes residue finiteness. No condition that
the relative algebraic closure of ℚ equals ℚ is needed. -/
theorem model_residuesFinite {N : ℕ} (M : Model N) : ResiduesFinite M := by
  letI : IsCurveField M.K := M.isCurveField
  intro P
  infer_instance

/-- Both order definitions use the same normalized DVR valuation.
The choices of proofs of IsDiscreteValuationRing agree by proof irrelevance. -/
theorem ord_eq_placeOrd {N : ℕ} (M : Model N) [IsCurveField M.K]
    (hDVR : PlacesDiscrete M) (P : Place M.K) (f : M.K) :
    ord M hDVR P f = P.ord f := rfl

end AbcAdaptation.Tripod.Fermat.Proper
