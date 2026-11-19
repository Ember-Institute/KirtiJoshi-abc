/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 9633c1cfca59895aff7c52e836464d9659abf445
Original path Iut/Tower/InertiaBound.lean
-/
import Solutions.Source_ReferenceIutVariableChangePoint
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.GalCompletion
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

/-- An inertia automorphism preserves the valuation at its place. -/
lemma valuation_map_eq_of_mem_inertia {k K : Type*} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] {w : FinitePlace K} {σ : K ≃ₐ[k] K}
    (hσ : σ ∈ w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K)) (a : K) :
    w.maximalIdeal.valuation K (σ a) = w.maximalIdeal.valuation K a := by
  have hw : JoshiTeich.ReferenceIut.galPlace σ w = w := by
    apply (FinitePlace.maximalIdeal_inj _ _).mp
    apply HeightOneSpectrum.ext
    rw [JoshiTeich.ReferenceIut.galPlace_maximalIdeal]
    refine Ideal.ext fun z => ?_
    change JoshiTeich.ReferenceIut.galRestrictInt σ⁻¹ z ∈ w.maximalIdeal.asIdeal ↔
      z ∈ w.maximalIdeal.asIdeal
    have hrestrict : JoshiTeich.ReferenceIut.galRestrictInt σ⁻¹ z = σ⁻¹ • z := by
      apply RingOfIntegers.coe_injective
      change (↑(JoshiTeich.ReferenceIut.galRestrictInt σ⁻¹ z) : K) = σ⁻¹ (z : K)
      exact JoshiTeich.ReferenceIut.coe_galRestrictInt σ⁻¹ z
    have hinv : σ⁻¹ ∈ w.maximalIdeal.asIdeal.inertia (K ≃ₐ[k] K) := Subgroup.inv_mem _ hσ
    have hdiff : σ⁻¹ • z - z ∈ w.maximalIdeal.asIdeal := hinv z
    rw [hrestrict, ← w.maximalIdeal.asIdeal.add_mem_iff_left (a := z) hdiff, add_sub_cancel]
  simpa only [hw] using JoshiTeich.ReferenceIut.galPlace_valuation σ w a

section VariableChange

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (σ : K →+* K)
  (hu : σ C.u = C.u) (hr : σ C.r = C.r) (hs : σ C.s = C.s) (ht : σ C.t = C.t)
include hu hr hs ht

omit hs ht in
/-- `vcX` commutes with `σ` when `σ` fixes the coefficients of `C`. -/
lemma vcX_map (x : K) : Anabelian.vcX C (σ x) = σ (Anabelian.vcX C x) := by
  unfold Anabelian.vcX
  rw [map_div₀, map_sub, map_pow, hu, hr]

/-- `vcY` commutes with `σ` when `σ` fixes the coefficients of `C`. -/
lemma vcY_map (x y : K) : Anabelian.vcY C (σ x) (σ y) = σ (Anabelian.vcY C x y) := by
  unfold Anabelian.vcY
  rw [map_div₀, map_sub, map_sub, map_mul, map_sub, map_pow, hu, hr, hs, ht]

open scoped Classical in
/-- **The conjugate of a coordinatewise action** by `vcEquiv C W` acts coordinatewise on
`C • W`. -/
lemma exists_vcEquiv_map_eq (φ : W.toAffine.Point →+ W.toAffine.Point)
    (hφ : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      ∃ h' : W.toAffine.Nonsingular (σ x) (σ y), φ (Point.some x y h) = Point.some (σ x) (σ y) h')
    (x' y' : K) (h' : (C • W).toAffine.Nonsingular x' y') :
    ∃ h'' : (C • W).toAffine.Nonsingular (σ x') (σ y'),
      Anabelian.vcEquiv C W (φ ((Anabelian.vcEquiv C W).symm (Point.some x' y' h'))) =
        Point.some (σ x') (σ y') h'' := by
  obtain ⟨Q, hQ⟩ := Anabelian.vcPoint_surjective C W (Point.some x' y' h')
  cases Q with
  | zero =>
    exact absurd (hQ.symm.trans (Anabelian.vcPoint_zero C W)) (Point.some_ne_zero h')
  | some x y h =>
    have hsymm : (Anabelian.vcEquiv C W).symm (Point.some x' y' h') = Point.some x y h := by
      rw [← hQ]
      exact (Anabelian.vcEquiv C W).symm_apply_apply (Point.some x y h)
    rw [Anabelian.vcPoint_some] at hQ
    obtain ⟨hσ, hφ'⟩ := hφ x y h
    obtain ⟨hx', hy'⟩ := Point.some.inj hQ
    subst hx' hy'
    refine ⟨?_, ?_⟩
    · rw [← vcX_map C σ hu hr, ← vcY_map C σ hu hr hs ht]
      exact (Anabelian.nonsingular_vc C W _ _).mp hσ
    · rw [hsymm, hφ', Anabelian.vcEquiv_apply, Anabelian.vcPoint_some]
      exact Anabelian.some_ext (vcX_map C σ hu hr x) (vcY_map C σ hu hr hs ht x y)

end VariableChange

/-- The iterates of a conjugate `e ∘ φ ∘ e⁻¹`. -/
lemma iterate_conj {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G') (φ : G →+ G)
    (m : ℕ) (Q : G) :
    (⇑(e.toAddMonoidHom.comp (φ.comp e.symm.toAddMonoidHom)))^[m] (e Q) = e ((⇑φ)^[m] Q) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp

/-! ### The Legendre coefficients of the twisted models -/

section Legendre

variable {K : Type*} [Field K] {μ : K} {W : Affine K} (hW₁ : W.a₁ = 0) (hW₂ : W.a₂ = -(1 + μ))
  (hW₃ : W.a₃ = 0) (hW₄ : W.a₄ = μ) (hW₆ : W.a₆ = 0)
include hW₁ hW₂ hW₃ hW₄ hW₆

/-- `⟨√−1, 1, 0, 0⟩ • E_μ` is the Legendre model of `1 − μ`. -/
lemma legendreCoeffs_vc_one_sub {i : K} (hi : i ^ 2 = -1) (hi0 : i ≠ 0) :
    let C : VariableChange K := ⟨Units.mk0 i hi0, 1, 0, 0⟩
    (C • W).a₁ = 0 ∧ (C • W).a₂ = -(1 + (1 - μ)) ∧ (C • W).a₃ = 0 ∧ (C • W).a₄ = 1 - μ ∧
      (C • W).a₆ = 0 := by
  intro C
  have h4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hi]; norm_num
  have h6 : i ^ 6 = -1 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hi]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [C, variableChange_a₁, hW₁]
  · simp only [C, variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hi, hW₁,
      hW₂]
    ring
  · simp [C, variableChange_a₃, hW₁, hW₃]
  · simp only [C, variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4, hW₁,
      hW₂, hW₃, hW₄]
    ring
  · simp only [C, variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h6, hW₁,
      hW₂, hW₃, hW₄, hW₆]
    ring

/-- `⟨√μ, 0, 0, 0⟩ • E_μ` is the Legendre model of `1/μ`. -/
lemma legendreCoeffs_vc_inv {u : K} (hu : u ^ 2 = μ) (hu0 : u ≠ 0) :
    let C : VariableChange K := ⟨Units.mk0 u hu0, 0, 0, 0⟩
    (C • W).a₁ = 0 ∧ (C • W).a₂ = -(1 + μ⁻¹) ∧ (C • W).a₃ = 0 ∧ (C • W).a₄ = μ⁻¹ ∧
      (C • W).a₆ = 0 := by
  intro C
  have hμ : μ ≠ 0 := by rw [← hu]; exact pow_ne_zero _ hu0
  have h4 : u ^ 4 = μ ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hu]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [C, variableChange_a₁, hW₁]
  · simp only [C, variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu, hW₁,
      hW₂]
    field_simp
    ring
  · simp [C, variableChange_a₃, hW₁, hW₃]
  · simp only [C, variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, h4, hW₁,
      hW₂, hW₃, hW₄]
    field_simp
    ring
  · simp only [C, variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hW₁, hW₂,
      hW₃, hW₄, hW₆]
    ring

end Legendre

section PointMap

variable {k K : Type*} [Field k] [Field K] [DecidableEq K] [Algebra k K] (W : WeierstrassCurve k)

/-- `Point.map (σ^m) = (Point.map σ)^[m]`. -/
lemma point_map_pow (σ : K ≃ₐ[k] K) (m : ℕ) (Q : (Affine.baseChange W K).Point) :
    Point.map (W' := W) (S := k) ((σ ^ m : K ≃ₐ[k] K) : K →ₐ[k] K) Q =
      (⇑(Point.map (W' := W) (S := k) (σ : K →ₐ[k] K)))^[m] Q := by
  induction m with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply]
    cases Q <;> rfl
  | succ m ih =>
    have : ((σ ^ (m + 1) : K ≃ₐ[k] K) : K →ₐ[k] K) =
        (σ : K →ₐ[k] K).comp ((σ ^ m : K ≃ₐ[k] K) : K →ₐ[k] K) :=
      AlgHom.ext fun x => by rw [pow_succ']; rfl
    rw [Function.iterate_succ_apply', ← ih, this, ← Point.map_map]

end PointMap

end AbcAdaptation.Reference.Iut
