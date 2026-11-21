import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_PointMap
import Theorems.Thm_AbcAdaptation_Reference_TateCurvesTheta_TateParameter_tatePoint_equation
import Theorems.Thm_AbcAdaptation_Reference_TateCurvesTheta_TateParameter_tatePoint_mul
import Theorems.Thm_AbcAdaptation_Reference_TateCurvesTheta_TateParameter_tatePoint_surjective

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve

variable {k : Type*} [Field k]

/-- The `x`-coordinate of a point (`0` at infinity). -/
def ptX {W : WeierstrassCurve k} : W.toAffine.Point → k
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point (`0` at infinity). -/
def ptY {W : WeierstrassCurve k} : W.toAffine.Point → k
  | .zero => 0
  | .some _ y _ => y

end AbcAdaptation.Reference.Iut.Anabelian

namespace AbcAdaptation.Reference.TateCurvesTheta.TateParameter

open AbcAdaptation.Reference.Iut.Anabelian
open scoped Classical

variable {k : Type*} [NormedField k] (t : TateParameter k)
  [CompleteSpace k] [IsUltrametricDist k]
variable (hmem : t.TatePointEquation) (h12 : (12 : k) ≠ 0)

lemma tatePoint_x (u : kˣ) (hu : ∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) :
    ptX (t.tatePoint hmem h12 u) = t.X u := by
  have h : u ∉ Subgroup.zpowers t.q := fun h => by
    obtain ⟨n, hn⟩ := (t.mem_zpowers_q_iff u).mp h
    exact hu n hn
  simp only [tatePoint, dif_neg h, ptX]

lemma tatePoint_y (u : kˣ) (hu : ∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) :
    ptY (t.tatePoint hmem h12 u) = t.Y u := by
  have h : u ∉ Subgroup.zpowers t.q := fun h => by
    obtain ⟨n, hn⟩ := (t.mem_zpowers_q_iff u).mp h
    exact hu n hn
  simp only [tatePoint, dif_neg h, ptY]

end AbcAdaptation.Reference.TateCurvesTheta.TateParameter

namespace AbcAdaptation.Reference.Iut

open AbcAdaptation.Reference.TateCurvesTheta Anabelian
open scoped Classical

noncomputable section

variable {k : Type*} [NormedField k]

/-- The uniformization of the curve defined by a Tate parameter, with its affine coordinate laws. -/
structure TateParameterUniformization (t : TateParameter k) where
  iso : Additive (kˣ ⧸ Subgroup.zpowers t.q) ≃+ t.tateCurve.toAffine.Point
  iso_x : ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * u ≠ 1) →
    ptX (iso (Additive.ofMul (QuotientGroup.mk u))) = t.X u
  iso_y : ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * u ≠ 1) →
    ptY (iso (Additive.ofMul (QuotientGroup.mk u))) = t.Y u

variable [CompleteSpace k] [IsUltrametricDist k]

/-- Descend the actual Tate point map to an additive equivalence and record its coordinates. -/
def TateParameterUniformization.ofTatePoint
    (t : TateParameter k) (hmem : t.TatePointEquation) (h12 : (12 : k) ≠ 0)
    (hadd : ∀ u v : kˣ, t.tatePoint hmem h12 (u * v) =
      t.tatePoint hmem h12 u + t.tatePoint hmem h12 v)
    (hsurj : Function.Surjective (t.tatePoint hmem h12)) :
    TateParameterUniformization t := by
  let f : kˣ →* Multiplicative t.tateCurve.toAffine.Point :=
    { toFun := fun u => Multiplicative.ofAdd (t.tatePoint hmem h12 u)
      map_one' := by
        change t.tatePoint hmem h12 1 = 0
        rw [t.tatePoint_eq_zero_iff hmem h12]
        exact one_mem _
      map_mul' := hadd }
  have hker : Subgroup.zpowers t.q = f.ker := by
    ext u
    rw [MonoidHom.mem_ker]
    change u ∈ Subgroup.zpowers t.q ↔ t.tatePoint hmem h12 u = 0
    rw [t.tatePoint_eq_zero_iff hmem h12]
  have hf : Function.Surjective f := by
    intro P
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd P)
    exact ⟨u, Multiplicative.toAdd.injective hu⟩
  let iso := QuotientGroup.liftEquiv (Subgroup.zpowers t.q) hf hker
  let isoAdd := MulEquiv.toAdditiveLeft iso
  have hmk (u : kˣ) :
      isoAdd (Additive.ofMul (QuotientGroup.mk u)) = t.tatePoint hmem h12 u := by
    change Multiplicative.toAdd (iso (QuotientGroup.mk u)) = t.tatePoint hmem h12 u
    rw [show iso (QuotientGroup.mk u) = f u from QuotientGroup.liftEquiv_mk _ _ _ _]
    rfl
  exact ⟨isoAdd, fun u hu => (congrArg ptX (hmk u)).trans (t.tatePoint_x hmem h12 u hu),
    fun u hu => (congrArg ptY (hmk u)).trans (t.tatePoint_y hmem h12 u hu)⟩

end

end AbcAdaptation.Reference.Iut

/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors

Original repository https://github.com/lana-agents/tate-curves-theta
Original revision ca6c2279d3cea0690cdb01328e727118d5485d68
Original paths TateCurvesTheta/TateCurve/TateUniformization.lean,
TateCurvesTheta/TateCurve/PointMap.lean and TateCurvesTheta/TateCurve/GroupLaw.lean
-/

set_option autoImplicit false

open AbcAdaptation.Reference.TateCurvesTheta WeierstrassCurve
open scoped Classical

/-- The quotient uniformization of a Tate curve has the Tate series as its coordinates. -/
theorem solution
    {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (t : TateParameter k) (h12 : (12 : k) ≠ 0) (h2 : ‖(2 : k)‖ = 1) :
    ∃ iso : Additive (kˣ ⧸ Subgroup.zpowers t.q) ≃+ t.tateCurve.toAffine.Point,
      (∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) →
        (match iso (Additive.ofMul (QuotientGroup.mk u)) with
          | .zero => 0
          | .some x _ _ => x) = t.X u) ∧
      (∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) →
        (match iso (Additive.ofMul (QuotientGroup.mk u)) with
          | .zero => 0
          | .some _ y _ => y) = t.Y u) := by
  let hmem := t.tatePoint_equation h12
  let uniformization :=
    AbcAdaptation.Reference.Iut.TateParameterUniformization.ofTatePoint t hmem h12
      (t.tatePoint_mul hmem h12 h2) (t.tatePoint_surjective hmem h12 h2)
  refine ⟨uniformization.iso, ?_, ?_⟩
  · intro u hu
    have hx := uniformization.iso_x u hu
    cases hp : uniformization.iso (Additive.ofMul (QuotientGroup.mk u)) <;>
      simpa only [AbcAdaptation.Reference.Iut.Anabelian.ptX, hp] using hx
  · intro u hu
    have hy := uniformization.iso_y u hu
    cases hp : uniformization.iso (Additive.ofMul (QuotientGroup.mk u)) <;>
      simpa only [AbcAdaptation.Reference.Iut.Anabelian.ptY, hp] using hy
