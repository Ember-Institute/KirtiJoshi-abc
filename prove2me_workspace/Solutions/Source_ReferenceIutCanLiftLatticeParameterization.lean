/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the upstream files.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Source is Oka/Uniformization/OncePunctured.lean at
75dcdc3faadd10b986afb9283e89902bcdddecd4 of https://github.com/lana-agents/oka.
-/
import Solutions.Source_ReferenceHeightsModularRange
import Solutions.Source_ReferenceHeightsWeierstrassFibers
import Solutions.Source_ReferenceHeightsWeierstrassSurjectivity
import Solutions.Source_ReferenceIutCanLiftDeckGroup
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped MatrixGroups UpperHalfPlane

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open AbcAdaptation.Reference.Heights
open WeierstrassCurve

/-- The Weierstrass parameterization followed by the change of coordinates to the
model `C • latticeCurve τ`. -/
noncomputable def latticeParameterization (τ : ℍ) (C : VariableChange ℂ) (z : ℂ) : ℂ × ℂ :=
  (vcX C ((periodPair τ).weierstrassP z),
    vcY C ((periodPair τ).weierstrassP z) ((periodPair τ).derivWeierstrassP z / 2))

theorem latticeParameterization_equation (τ : ℍ) (C : VariableChange ℂ) {z : ℂ}
    (hz : z ∉ (periodPair τ).lattice) :
    (C • latticeCurve τ).toAffine.Equation
      (latticeParameterization τ C z).1 (latticeParameterization τ C z).2 := by
  simp only [latticeParameterization]
  apply (equation_vc C (latticeCurve τ) _ _).mp
  rw [Affine.equation_iff]
  simp only [latticeCurve, zero_mul, add_zero]
  have h := (periodPair τ).derivWeierstrassP_sq z hz
  linear_combination h / 4

theorem latticeParameterization_surjective (τ : ℍ) (C : VariableChange ℂ) {x y : ℂ}
    (hxy : (C • latticeCurve τ).toAffine.Equation x y) :
    ∃ z ∉ (periodPair τ).lattice, latticeParameterization τ C z = (x, y) := by
  let X := (C.u : ℂ) ^ 2 * x + C.r
  let Y := (C.u : ℂ) ^ 3 * y + (C.u : ℂ) ^ 2 * C.s * x + C.t
  have hX : vcX C X = x := vcX_of C x
  have hY : vcY C X Y = y := vcY_of C x y
  have hE : (latticeCurve τ).toAffine.Equation X Y :=
    (equation_vc C (latticeCurve τ) X Y).mpr (by rwa [hX, hY])
  have : (latticeCurve τ).IsElliptic := latticeCurve_isElliptic τ
  have hns := Affine.equation_iff_nonsingular.mp hE
  obtain ⟨z, hz⟩ := latticePointMap_surjective τ (Affine.Point.some X Y hns)
  by_cases hm : z ∈ (periodPair τ).lattice
  · rw [latticePointMap_of_mem hm] at hz
    exact (Affine.Point.some_ne_zero hns hz.symm).elim
  · rw [latticePointMap_of_notMem hm] at hz
    simp only [Affine.Point.some.injEq] at hz
    exact ⟨z, hm, by simp only [latticeParameterization, hz.1, hz.2, hX, hY]⟩

theorem latticeParameterization_eq_iff (τ : ℍ) (C : VariableChange ℂ) {z w : ℂ}
    (hz : z ∉ (periodPair τ).lattice) (hw : w ∉ (periodPair τ).lattice) :
    latticeParameterization τ C z = latticeParameterization τ C w ↔
      z - w ∈ (periodPair τ).lattice := by
  let L := periodPair τ
  have hcoordinates := weierstrassP_deriv_eq_iff_sub_mem L z w hz hw
  constructor
  · intro h
    have hx : L.weierstrassP z = L.weierstrassP w :=
      vcX_injective C (congrArg Prod.fst h)
    have hy : vcY C (L.weierstrassP z) (L.derivWeierstrassP z / 2) =
        vcY C (L.weierstrassP w) (L.derivWeierstrassP w / 2) := congrArg Prod.snd h
    rw [hx] at hy
    have hdivide := (vcY_inj C _ _ _).mp hy
    exact hcoordinates.mp ⟨hx, (div_left_inj' (two_ne_zero : (2 : ℂ) ≠ 0)).mp hdivide⟩
  · intro h
    obtain ⟨hx, hy⟩ := hcoordinates.mpr h
    change (vcX C (L.weierstrassP z), vcY C (L.weierstrassP z) (L.derivWeierstrassP z / 2)) =
      (vcX C (L.weierstrassP w), vcY C (L.weierstrassP w) (L.derivWeierstrassP w / 2))
    rw [hx, hy]

private theorem deriv_deriv_ne_zero_of_deriv_eq_zero (τ : ℍ) {z : ℂ}
    (hz : z ∉ (periodPair τ).lattice) (h₁ : (periodPair τ).derivWeierstrassP z = 0) :
    deriv (periodPair τ).derivWeierstrassP z ≠ 0 := by
  rw [deriv_derivWeierstrassP _ _ hz]
  intro h₂
  have hsquare := (periodPair τ).derivWeierstrassP_sq z hz
  rw [h₁] at hsquare
  have hg₂ : (periodPair τ).g₂ = 12 * (periodPair τ).weierstrassP z ^ 2 := by
    linear_combination -2 * h₂
  have hg₃ : (periodPair τ).g₃ = -8 * (periodPair τ).weierstrassP z ^ 3 := by
    rw [hg₂] at hsquare
    linear_combination hsquare
  have : (latticeCurve τ).IsElliptic := latticeCurve_isElliptic τ
  apply (latticeCurve τ).isUnit_Δ.ne_zero
  rw [latticeCurve_discriminant, hg₂, hg₃]
  ring

/-- The Weierstrass parameterization is a holomorphic immersion away from the
period lattice. -/
theorem latticeParameterization_immersion (τ : ℍ) (C : VariableChange ℂ) {z : ℂ}
    (hz : z ∉ (periodPair τ).lattice) :
    DifferentiableAt ℂ (latticeParameterization τ C) z ∧
      deriv (latticeParameterization τ C) z ≠ 0 := by
  let L := periodPair τ
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    rw [← PeriodPair.deriv_weierstrassP]
    exact (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hp' := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have hX := (hp.sub_const C.r).div_const ((C.u : ℂ) ^ 2)
  have hY := (((hp'.div_const 2).sub_const C.t).sub
    ((hp.sub_const C.r).const_mul C.s)).div_const ((C.u : ℂ) ^ 3)
  have hd := hX.prodMk hY
  change HasDerivAt (latticeParameterization τ C)
    (L.derivWeierstrassP z / (C.u : ℂ) ^ 2,
      (deriv L.derivWeierstrassP z / 2 - C.s * L.derivWeierstrassP z) / (C.u : ℂ) ^ 3) z at hd
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  intro hzero
  have hx : L.derivWeierstrassP z / (C.u : ℂ) ^ 2 = 0 := congrArg Prod.fst hzero
  have hy : (deriv L.derivWeierstrassP z / 2 - C.s * L.derivWeierstrassP z) /
      (C.u : ℂ) ^ 3 = 0 := congrArg Prod.snd hzero
  have h₁ := (div_eq_zero_iff.mp hx).resolve_right (pow_ne_zero _ C.u.ne_zero)
  have h₂ : deriv L.derivWeierstrassP z / 2 = 0 := by
    simpa only [h₁, mul_zero, sub_zero] using
      (div_eq_zero_iff.mp hy).resolve_right (pow_ne_zero _ C.u.ne_zero)
  exact deriv_deriv_ne_zero_of_deriv_eq_zero τ hz h₁
    ((div_eq_zero_iff.mp h₂).resolve_right two_ne_zero)

/-- Every element of `⟨A, B, -1⟩` acts on `ℍ` as an element of `⟨A, B⟩`. -/
private theorem exists_smul_eq_in_closure {A B g : SL(2, ℝ)}
    (hg : g ∈ IsUniformization.pmGroup A B) :
    ∃ γ ∈ Subgroup.closure {A, B}, ∀ z : ℍ, γ • z = g • z := by
  change g ∈ Subgroup.closure {A, B, -1} at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    have hgen : g ∈ ({A, B} : Set SL(2, ℝ)) ∨ g = -1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] using hg
    rcases hgen with hs | rfl
    · exact ⟨g, Subgroup.subset_closure hs, fun _ ↦ rfl⟩
    · exact ⟨1, one_mem _, fun z ↦ by rw [one_smul, neg_one_act]⟩
  | one => exact ⟨1, one_mem _, fun z ↦ rfl⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    obtain ⟨γ₁, hγ₁, h₁⟩ := ih₁
    obtain ⟨γ₂, hγ₂, h₂⟩ := ih₂
    exact ⟨γ₁ * γ₂, mul_mem hγ₁ hγ₂, fun z ↦ by rw [mul_smul, mul_smul, h₂, h₁]⟩
  | inv g _ ih =>
    obtain ⟨γ, hγ, h⟩ := ih
    exact ⟨γ⁻¹, inv_mem hγ, fun z ↦ by
      rw [inv_smul_eq_iff, h (g⁻¹ • z), smul_inv_smul]⟩

/-- Composing a lattice-complement uniformization with the Weierstrass parameterization gives
a uniformization of the affine curve. The lattice fibers may use both signs of a deck matrix. -/
theorem isUniformization_latticeParameterization (τ : ℍ) (C : VariableChange ℂ)
    {A B : SL(2, ℝ)} {ψ : ℂ → ℂ}
    (hnotMem : ∀ z : ℍ, ψ z ∉ (periodPair τ).lattice)
    (hψ : ∀ z : ℍ, DifferentiableAt ℂ ψ z ∧ deriv ψ z ≠ 0)
    (hsurj : ∀ w ∉ (periodPair τ).lattice, ∃ z : ℍ, ψ z = w)
    (hfibre : ∀ z w : ℍ, ψ w - ψ z ∈ (periodPair τ).lattice ↔
      ∃ γ ∈ IsUniformization.pmGroup A B, γ • z = w) :
    IsUniformization (C • latticeCurve τ) A B (latticeParameterization τ C ∘ ψ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    have hparam := latticeParameterization_immersion τ C (hnotMem z)
    have hderiv := hparam.1.hasDerivAt.scomp (z : ℂ) (hψ z).1.hasDerivAt
    refine ⟨hderiv.differentiableAt, ?_⟩
    rw [hderiv.deriv]
    exact smul_ne_zero (hψ z).2 hparam.2
  · intro z
    exact latticeParameterization_equation τ C (hnotMem z)
  · intro x y hxy
    obtain ⟨w, hw, hparam⟩ := latticeParameterization_surjective τ C hxy
    obtain ⟨z, hz⟩ := hsurj w hw
    exact ⟨z, (congrArg (latticeParameterization τ C) hz).trans hparam⟩
  · intro z w
    have hPeriod :
        (latticeParameterization τ C ∘ ψ) z = (latticeParameterization τ C ∘ ψ) w ↔
          ψ w - ψ z ∈ (periodPair τ).lattice :=
      eq_comm.trans (latticeParameterization_eq_iff τ C (hnotMem w) (hnotMem z))
    rw [hPeriod, hfibre z w]
    constructor
    · rintro ⟨γ, hγ, hγz⟩
      obtain ⟨δ, hδ, hδγ⟩ := exists_smul_eq_in_closure hγ
      exact ⟨δ, hδ, (hδγ z).trans hγz⟩
    · rintro ⟨γ, hγ, hγz⟩
      exact ⟨γ, IsUniformization.closure_le_pmGroup A B hγ, hγz⟩

/-- Every complex elliptic curve is a change of variables of a short lattice model. -/
theorem exists_variableChange_latticeCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (τ : ℍ) (C : VariableChange ℂ), C • latticeCurve τ = W := by
  obtain ⟨τ, hτ⟩ := modularJ_surjective W.j
  have : (latticeCurve τ).IsElliptic := latticeCurve_isElliptic τ
  obtain ⟨C, hC⟩ := (latticeCurve τ).exists_variableChange_of_j_eq W
    ((latticeCurve_j_eq_modularJ τ).trans hτ)
  exact ⟨τ, C, hC⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
