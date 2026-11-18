/-
Adapted from TateCurvesTheta/TateCurve/PointMap.lean, GroupLaw.lean,
and TateUniformization.lean, lana-agents/tate-curves-theta at
ca6c2279d3cea0690cdb01328e727118d5485d68.
The point map uses the adapted Tate series. Its affine equation, additivity
and surjectivity are the analytic inputs.
-/
/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Parametrization
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.QuotientGroup.Defs
import Solutions.Source_ReferenceIutVariableChangePoint

namespace AbcAdaptation.Reference

open WeierstrassCurve Iut.Anabelian
open scoped Classical

noncomputable section

namespace TateCurvesTheta.TateParameter

variable {k : Type*} [NormedField k] (t : TateParameter k)

lemma mem_zpowers_q_iff (u : kˣ) :
    u ∈ Subgroup.zpowers t.q ↔ ∃ n : ℤ, (t.q : k) ^ n * (u : k) = 1 := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have hu : (u : k) = (t.q : k) ^ n := by rw [← hn, Units.val_zpow_eq_zpow_val]
    rw [hu, ← zpow_add₀ t.q.ne_zero, neg_add_cancel, zpow_zero]
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zpow_neg]
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one]
    exact hn

/-- The Weierstrass equation for the Tate coordinate series away from the powers of the parameter. -/
def TatePointEquation : Prop :=
  ∀ u : kˣ, (∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)

variable [CompleteSpace k] [IsUltrametricDist k]
variable (hmem : t.TatePointEquation) (h12 : (12 : k) ≠ 0)

/-- The Tate point at a unit is the point at infinity on the powers of the parameter.
Its affine coordinates elsewhere are the Tate series. -/
def tatePoint (u : kˣ) : t.tateCurve.toAffine.Point :=
  if hu : u ∈ Subgroup.zpowers t.q then 0
  else
    .some (t.X u) (t.Y u) <|
      (t.tateCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        (t.tateCurve_Δ_ne_zero h12)).mp <|
        hmem u fun n hn => hu ((t.mem_zpowers_q_iff u).mpr ⟨n, hn⟩)

lemma tatePoint_eq_zero_iff (u : kˣ) :
    t.tatePoint hmem h12 u = 0 ↔ u ∈ Subgroup.zpowers t.q := by
  by_cases hu : u ∈ Subgroup.zpowers t.q
  · simp [tatePoint, hu]
  · rw [tatePoint, dif_neg hu]
    exact ⟨fun h => (Affine.Point.some_ne_zero _ h).elim, fun h => (hu h).elim⟩

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

end TateCurvesTheta.TateParameter

namespace Iut

open TateCurvesTheta
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

end Iut

end

end AbcAdaptation.Reference
