/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original paths Oka/Uniformization/{FEtTransitive,Integrality}.lean
-/
import Solutions.Source_ReferenceIutCanLiftAnalyticCovering
import Solutions.Source_ReferenceIutCanLiftHalfPlaneAut
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped BigOperators MatrixGroups

/-- Coefficients of `∏ (X - a i)` are bounded by `∏ (1 + |a i|)`. -/
theorem norm_coeff_prod_X_sub_C_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (k : ℕ) :
    ‖(∏ i ∈ s, (X - C (a i))).coeff k‖ ≤ ∏ i ∈ s, (1 + ‖a i‖) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]
    split_ifs <;> norm_num
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_comm (X - C _)]
    have hM : 0 ≤ ∏ i ∈ s, (1 + ‖a i‖) := Finset.prod_nonneg fun i _ ↦ by positivity
    cases k with
    | zero =>
      rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, norm_mul, norm_neg]
      nlinarith [ih 0, norm_nonneg (a j), norm_nonneg ((∏ i ∈ s, (X - C (a i))).coeff 0)]
    | succ k =>
      rw [coeff_mul_X_sub_C]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      nlinarith [ih k, ih (k + 1), norm_nonneg (a j),
        norm_nonneg ((∏ i ∈ s, (X - C (a i))).coeff (k + 1))]

/-- Coefficients of `∏ (X - a i z)` depend holomorphically on `z`. -/
theorem differentiableOn_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι) {a : ι → ℂ → ℂ}
    {S : Set ℂ} (ha : ∀ i ∈ s, DifferentiableOn ℂ (a i) S) (k : ℕ) :
    DifferentiableOn ℂ (fun z ↦ (∏ i ∈ s, (X - C (a i z))).coeff k) S := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => exact differentiableOn_const _
  | insert j s hj ih =>
    have ih' := ih fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
    have hj' := ha j (Finset.mem_insert_self j s)
    cases k with
    | zero =>
      have e : (fun z ↦ (∏ i ∈ insert j s, (X - C (a i z))).coeff 0) =
          fun z ↦ (∏ i ∈ s, (X - C (a i z))).coeff 0 * -a j z := by
        funext z
        rw [Finset.prod_insert hj, mul_comm (X - C _), mul_coeff_zero, coeff_sub, coeff_X_zero,
          coeff_C_zero, zero_sub]
      rw [e]
      exact (ih' 0).mul hj'.neg
    | succ k =>
      have e : (fun z ↦ (∏ i ∈ insert j s, (X - C (a i z))).coeff (k + 1)) =
          fun z ↦ (∏ i ∈ s, (X - C (a i z))).coeff k -
            (∏ i ∈ s, (X - C (a i z))).coeff (k + 1) * a j z := by
        funext z
        rw [Finset.prod_insert hj, mul_comm (X - C _), coeff_mul_X_sub_C]
      rw [e]
      exact (ih' k).sub ((ih' (k + 1)).mul hj')

theorem HolH.comp_smul {g : ℍ → ℂ} (hg : HolH g) (γ : SL(2, ℝ)) : HolH fun τ ↦ g (γ • τ) := by
  unfold HolH at *
  have hγ : DifferentiableOn ℂ (fun z ↦ ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1))
      {z | 0 < z.im} :=
    (((differentiableOn_const _).mul differentiableOn_id).add_const _).div
      (((differentiableOn_const _).mul differentiableOn_id).add_const _)
      fun z hz ↦ denom_SL2R_ne_zero γ hz
  have hmaps : MapsTo (fun z ↦ ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1))
      {z | 0 < z.im} {z | 0 < z.im} := fun z hz ↦ by
    have := (γ • (⟨z, hz⟩ : ℍ)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_SL2R_smul] at this
  refine (hg.comp hγ hmaps).congr fun z hz ↦ ?_
  simp only [Function.comp_apply]
  congr 1
  apply UpperHalfPlane.ext
  rw [ofComplex_of_im_pos (hmaps hz), ofComplex_apply_of_im_pos hz, coe_SL2R_smul]

namespace PolyBdd

variable {h₀ : ℍ → ℂ}

theorem prod {ι : Type*} (s : Finset ι) {u : ι → ℍ → ℝ} (hu : ∀ i ∈ s, PolyBdd h₀ (u i))
    (hu0 : ∀ i ∈ s, ∀ τ, 0 ≤ u i τ) : PolyBdd h₀ fun τ ↦ ∏ i ∈ s, u i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | insert j s hj ih =>
    simp_rw [Finset.prod_insert hj]
    exact mul (hu j (Finset.mem_insert_self _ _))
      (ih (fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hu0 i (Finset.mem_insert_of_mem hi))
      (hu0 j (Finset.mem_insert_self _ _))
      fun τ ↦ Finset.prod_nonneg fun i hi ↦ hu0 i (Finset.mem_insert_of_mem hi) τ

theorem sum {ι : Type*} (s : Finset ι) {u : ι → ℍ → ℝ} (hu : ∀ i ∈ s, PolyBdd h₀ (u i)) :
    PolyBdd h₀ fun τ ↦ ∑ i ∈ s, u i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert j s hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact add (hu j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi))

end PolyBdd

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B] [Algebra A B]
  {ι₀ : A →ₐ[ℂ] (ℍ → ℂ)}

/-- Invariance transports points. -/
def Over.transport {χ χ' : A →ₐ[ℂ] ℂ} (h : χ = χ') (ψ : Over B χ) : Over B χ' := h ▸ ψ

theorem Over.transport_coe {χ χ' : A →ₐ[ℂ] ℂ} (h : χ = χ') (ψ : Over B χ) :
    ⇑(ψ.transport h).1 = ⇑ψ.1 := by subst h; rfl

theorem IsLift.smul {Γ : Subgroup SL(2, ℝ)} (hΓ : ∀ γ ∈ Γ, ∀ a τ, ι₀ a (γ • τ) = ι₀ a τ)
    {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) {γ : SL(2, ℝ)} (hγ : γ ∈ Γ) :
    IsLift ι₀ fun τ ↦ ι (γ • τ) := by
  have hγc : Continuous (fun τ : ℍ ↦ γ • τ) := by
    change Continuous (fun τ : ℍ ↦ Matrix.SpecialLinearGroup.mapGL ℝ γ • τ)
    exact continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)
  refine ⟨fun τ ↦ ?_, fun b ↦ (h.cont b).comp hγc⟩
  obtain ⟨ψ, hψ⟩ := h.pt (γ • τ)
  have hpt : CanLiftAnalytic.pt ι₀ (γ • τ) = CanLiftAnalytic.pt ι₀ τ :=
    AlgHom.ext fun a ↦ hΓ γ hγ a τ
  exact ⟨ψ.transport hpt, by rw [Over.transport_coe, hψ]⟩

/-- A lift of an injective `ι₀` to a domain integral over `A` is injective. -/
theorem IsLift.eq_zero [IsDomain B] [Algebra.IsIntegral A B] (hinj : Function.Injective ι₀)
    {ι : ℍ → B → ℂ} (h : IsLift ι₀ ι) {b : B} (hb : ∀ τ, ι τ b = 0) : b = 0 := by
  classical
  by_contra hb0
  have : Nontrivial A := ⟨⟨1, 0, fun h ↦ by
    have := congrFun (congrArg ι₀ h) UpperHalfPlane.I; simp at this⟩⟩
  have hint : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have hGm : (minpoly A b).Monic := minpoly.monic hint
  have hG : aeval b (minpoly A b) = 0 := minpoly.aeval A b
  have hG0 : (minpoly A b).coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨H, hH⟩ := X_dvd_iff.mpr h0
    have hHm : H.Monic := Monic.of_mul_monic_left monic_X (hH ▸ hGm)
    have hHb : aeval b H = 0 := by
      rw [hH, map_mul, aeval_X] at hG
      exact (mul_eq_zero.mp hG).resolve_left hb0
    have hmin := minpoly.min A b hHm hHb
    rw [hH, mul_comm, degree_mul_X, degree_eq_natDegree hHm.ne_zero] at hmin
    have : ((H.natDegree + 1 : ℕ) : WithBot ℕ) ≤ (H.natDegree : WithBot ℕ) := by
      push_cast; exact hmin
    norm_cast at this
    omega
  apply hG0
  apply hinj
  funext τ
  obtain ⟨ψ, hψ⟩ := h.pt τ
  have hdec := divX_mul_X_add (minpoly A b)
  have h1 : aeval b (minpoly A b) = aeval b (divX (minpoly A b)) * b +
      algebraMap A B ((minpoly A b).coeff 0) := by
    conv_lhs => rw [← hdec]
    simp [map_add, map_mul]
  rw [hG] at h1
  have h2 := congrArg ψ.1 h1
  rw [map_zero, map_add, map_mul, ψ.2, hψ, hb τ, mul_zero, zero_add, pt_apply] at h2
  rw [← h2]
  simp

/-- Cauchy's bound for a root of a monic polynomial. -/
theorem norm_le_of_isRoot_monic {p : ℂ[X]} (hp : p.Monic) {r : ℂ} (hr : p.IsRoot r) :
    ‖r‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ := by
  have h := hr.norm_lt_cauchyBound hp.ne_zero
  have hc : cauchyBound p ≤ (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) + 1 := by
    rw [cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi ↦
      Finset.single_le_sum (f := fun i ↦ ‖p.coeff i‖₊) (fun _ _ ↦ zero_le) hi
  have h2 : (‖r‖₊ : ℝ) ≤ ((∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) + 1 : NNReal) :=
    NNReal.coe_le_coe.mpr (h.le.trans hc)
  push_cast at h2
  linarith

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
