/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Original repository https://github.com/lana-agents/oka
Original revision 75dcdc3faadd10b986afb9283e89902bcdddecd4
Original path Oka/Uniformization/CommutatorTrace.lean
-/
import Solutions.Source_ReferenceIutCanLiftLatticeParabolicMonodromy
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# The traces of the edge pairings and their commutator

Trace `2` for the puncture monodromy would force the edge pairings to share a real boundary
fixed point. Conjugating to that point reduces the monodromy to a translation. Shrinking
its conjugates would violate local injectivity of the covering. If both upper triangular
generators have diagonal entries of modulus one, their commutator acts trivially.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic

namespace Peripheral

open AbcAdaptation.Reference.Heights Generators

variable {t : ℍ} (U : LatticeComplementCover (periodPair t))


theorem A_smul_ne (τ : ℍ) : A U • τ ≠ τ := by
  intro h
  have := ψ_A_smul U τ
  rw [h] at this
  simp at this

theorem trace_sq_A : 4 ≤ trSL (A U) ^ 2 := by
  by_contra h
  push Not at h
  obtain ⟨τ, hτ⟩ := exists_smul_eq_self_of_trace_sq_lt (A U) h
  exact A_smul_ne U τ hτ

theorem trSL_A_ne_zero : trSL (A U) ≠ 0 := by
  intro h
  have := trace_sq_A U
  rw [h] at this; norm_num at this

/-- `ψ` is injective near every point. -/
theorem exists_nhds_injOn (ν : ℍ) : ∃ W ∈ 𝓝 ν, InjOn U.ψ W := by
  obtain ⟨φ, hν, hφ⟩ := U.covering.isLocalHomeomorphOn ν (U.ψ_notMem ν)
  refine ⟨φ.source, φ.open_source.mem_nhds hν, fun a ha b hb hab ↦ φ.injOn ha hb ?_⟩
  rw [← hφ]; exact hab

theorem ψ_conj_smul {X g : SL(2, ℝ)} (hX : X ∈ U.deckGroup) (hg : ∀ ν, U.ψ (g • ν) = U.ψ ν)
    (ν : ℍ) : U.ψ ((X * g * X⁻¹) • ν) = U.ψ ν := by
  obtain ⟨l, -, hl⟩ := hX
  have h1 : U.ψ (X⁻¹ • ν) = U.ψ ν - l := by
    have := hl (X⁻¹ • ν); rw [smul_inv_smul] at this; rw [this]; ring
  rw [mul_smul, mul_smul, hl, hg, h1]; ring

theorem ψ_pow_conj_smul {X : SL(2, ℝ)} (hX : X ∈ U.deckGroup) (n : ℕ) (ν : ℍ) :
    U.ψ ((X ^ n * Cm U * (X ^ n)⁻¹) • ν) = U.ψ ν := by
  induction n generalizing ν with
  | zero => simpa using ψ_Cm_smul U ν
  | succ n ih =>
    have e : X ^ (n + 1) * Cm U * (X ^ (n + 1))⁻¹ = X * (X ^ n * Cm U * (X ^ n)⁻¹) * X⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    rw [e]; exact ψ_conj_smul U hX ih ν

/-- The upper unipotent normal form of `C` after conjugation by `M`. -/
def Unipotent (V : SL(2, ℝ)) : Prop := V 1 0 = 0 ∧ V 0 0 = 1 ∧ V 1 1 = 1

/-- **No accumulation**: a deck transformation `X`, upper triangular after conjugation by `M` with
upper left entry of modulus `< 1`, cannot exist when `M⁻¹ C M` is a nontrivial translation. -/
theorem no_accumulation {X M : SL(2, ℝ)} (hX : X ∈ U.deckGroup) (hX0 : (M⁻¹ * X * M) 1 0 = 0)
    (hx : |(M⁻¹ * X * M) 0 0| < 1) (hC : Unipotent (M⁻¹ * Cm U * M))
    (hτ : (M⁻¹ * Cm U * M) 0 1 ≠ 0) : False := by
  set X₀ := M⁻¹ * X * M
  set C₀ := M⁻¹ * Cm U * M
  set x := X₀ 0 0
  set τ := C₀ 0 1
  have hx0 : x ≠ 0 := by
    intro h
    have := det_SL X₀
    rw [hX0, show X₀ 0 0 = x from rfl, h] at this
    simp at this
  have hconj : ∀ n : ℕ, M⁻¹ * (X ^ n * Cm U * (X ^ n)⁻¹) * M = X₀ ^ n * C₀ * (X₀ ^ n)⁻¹ := by
    intro n
    have hpow : X₀ ^ n = M⁻¹ * X ^ n * M := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ih, pow_succ]; simp only [X₀]; group
    rw [hpow]; simp only [C₀]; group
  set ν₀ : ℍ := M • UpperHalfPlane.I
  have hact : ∀ n : ℕ, (X ^ n * Cm U * (X ^ n)⁻¹) • ν₀ =
      M • ((X₀ ^ n * C₀ * (X₀ ^ n)⁻¹) • UpperHalfPlane.I) := by
    intro n
    rw [← hconj n, ← mul_smul, ← mul_smul]
    congr 1
    group
  have hcoe : ∀ n : ℕ, (((X₀ ^ n * C₀ * (X₀ ^ n)⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) =
      I + (x ^ (2 * n) * τ : ℝ) := by
    intro n
    obtain ⟨h1, h2, h3, h4⟩ := pow_conj_unipotent hX0 hC n
    rw [coe_unipotent_smul_I ⟨h1, h2, h3⟩, h4]
  -- convergence
  have hlim0 : Tendsto (fun n : ℕ ↦ x ^ (2 * n) * τ) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ (x ^ 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by
        rw [abs_of_nonneg (sq_nonneg x)]
        nlinarith [abs_nonneg x, sq_abs x, abs_mul_abs_self x])
    have := this.mul_const τ
    simpa [pow_mul] using this
  have hlimH : Tendsto (fun n : ℕ ↦ (X₀ ^ n * C₀ * (X₀ ^ n)⁻¹) • UpperHalfPlane.I) atTop
      (𝓝 UpperHalfPlane.I) := by
    rw [isOpenEmbedding_coe.isInducing.tendsto_nhds_iff]
    simp only [Function.comp_def, hcoe]
    have : Tendsto (fun n : ℕ ↦ I + ((x ^ (2 * n) * τ : ℝ) : ℂ)) atTop (𝓝 (I + ((0 : ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.continuousAt.tendsto.comp hlim0)
    simpa using this
  have hlim : Tendsto (fun n : ℕ ↦ (X ^ n * Cm U * (X ^ n)⁻¹) • ν₀) atTop (𝓝 ν₀) := by
    simp only [hact]
    exact ((continuous_const_smul M).tendsto _).comp hlimH
  obtain ⟨W, hW, hinj⟩ := exists_nhds_injOn U ν₀
  obtain ⟨n, hn⟩ := (hlim.eventually (show W ∈ 𝓝 ν₀ from hW)).exists_forall_of_atTop
  have hmem := hn (n + 1) (by omega)
  have heq := hinj hmem (mem_of_mem_nhds hW) (ψ_pow_conj_smul U hX (n + 1) ν₀)
  rw [hact, smul_left_cancel_iff] at heq
  have := congrArg (fun z : ℍ ↦ (z : ℂ)) heq
  simp only [hcoe, UpperHalfPlane.coe_I] at this
  have h0 : (x ^ (2 * (n + 1)) * τ : ℝ) = 0 := by exact_mod_cast (by simpa using this)
  rcases mul_eq_zero.mp h0 with h | h
  · exact hx0 (pow_eq_zero_iff (by omega) |>.mp h)
  · exact hτ h

theorem trSL_BA_comm : trSL (B U * A U * (B U)⁻¹ * (A U)⁻¹) = trSL (Cm U) := by
  have e : B U * A U * (B U)⁻¹ * (A U)⁻¹ =
      ((A U)⁻¹ * (B U)⁻¹)⁻¹ * (Cm U)⁻¹ * ((A U)⁻¹ * (B U)⁻¹) := by
    simp only [Cm]; group
  rw [e, trSL_conj, trSL_inv]

theorem exists_upper_A : ∃ M₁ : SL(2, ℝ), (M₁⁻¹ * A U * M₁) 1 0 = 0 := by
  by_cases hc : A U 1 0 = 0
  · exact ⟨1, by simpa using hc⟩
  · obtain ⟨η, hη⟩ := exists_real_fix (A U) (trace_sq_A U) hc
    exact ⟨conjFix η, by rw [conjFix_lowerLeft]; exact hη⟩

/-- If `tr C = 2`, then `A` and `B` have a common fixed point on `∂ℍ`. -/
theorem exists_common_upper (h2 : trSL (Cm U) = 2) :
    ∃ M : SL(2, ℝ), (M⁻¹ * A U * M) 1 0 = 0 ∧ (M⁻¹ * B U * M) 1 0 = 0 := by
  obtain ⟨M₁, hA₁⟩ := exists_upper_A U
  set A₁ := M₁⁻¹ * A U * M₁
  set B₁ := M₁⁻¹ * B U * M₁
  have htr : trSL (B₁ * A₁ * B₁⁻¹ * A₁⁻¹) = 2 := by
    have e : B₁ * A₁ * B₁⁻¹ * A₁⁻¹ = M₁⁻¹ * (B U * A U * (B U)⁻¹ * (A U)⁻¹) * M₁ := by
      simp only [A₁, B₁]; group
    rw [e, trSL_conj, trSL_BA_comm, h2]
  have hkey := trace_commutator_sub_two B₁ A₁ hA₁
  rw [htr, sub_self] at hkey
  rcases mul_eq_zero.mp hkey.symm with hB | hE
  · exact ⟨M₁, hA₁, hB⟩
  set y := A₁ 0 0; set s := A₁ 0 1; set w := A₁ 1 1
  have hdet : y * w = 1 := by have := det_SL A₁; rw [hA₁] at this; linarith
  by_cases hwy : w = y
  · -- then `s = 0` (unless `B₁` is upper triangular) and `A₁ = ±1` fixes `i`
    by_cases hB : B₁ 1 0 = 0
    · exact ⟨M₁, hA₁, hB⟩
    exfalso
    have hs : s = 0 := by
      have : B₁ 1 0 * s ^ 2 = 0 := by
        have := hE; simp only [hwy, sub_self] at this; linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hB
      · exact pow_eq_zero_iff two_ne_zero |>.mp h
    have hy : y ≠ 0 := by rintro h; rw [h, zero_mul] at hdet; exact zero_ne_one hdet
    have hfix : A₁ • UpperHalfPlane.I = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext
      rw [coe_SL2R_smul, hA₁, show A₁ 0 1 = s from rfl, hs, show A₁ 1 1 = w from rfl, hwy]
      simp only [UpperHalfPlane.coe_I]
      change ((y : ℂ) * I + ((0 : ℝ) : ℂ)) / (((0 : ℝ) : ℂ) * I + y) = I
      push_cast
      have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
      rw [add_zero, zero_mul, zero_add, mul_div_cancel_left₀ _ hy']
    apply A_smul_ne U (M₁ • UpperHalfPlane.I)
    rw [← mul_smul, show A U * M₁ = M₁ * A₁ by simp only [A₁]; group, mul_smul, hfix]
  · -- the second fixed point `η = s / (w - y)` of `A₁` is fixed by `B₁`
    have hwy' : w - y ≠ 0 := sub_ne_zero.mpr hwy
    set η := s / (w - y)
    refine ⟨M₁ * conjFix η, ?_, ?_⟩
    · rw [show (M₁ * conjFix η)⁻¹ * A U * (M₁ * conjFix η) = (conjFix η)⁻¹ * A₁ * conjFix η by
        simp only [A₁]; group, conjFix_lowerLeft, hA₁]
      simp only [η, show A₁ 1 1 = w from rfl, show A₁ 0 0 = y from rfl, show A₁ 0 1 = s from rfl]
      field_simp; ring
    · rw [show (M₁ * conjFix η)⁻¹ * B U * (M₁ * conjFix η) = (conjFix η)⁻¹ * B₁ * conjFix η by
        simp only [B₁]; group, conjFix_lowerLeft]
      simp only [η]
      field_simp
      linear_combination hE

/-- **The trace of the monodromy is `-2`.** -/
theorem trace_Cm : trSL (Cm U) = -2 := by
  have h4 := trace_sq_eq U
  have : (trSL (Cm U) - 2) * (trSL (Cm U) + 2) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp this with h | h
  swap; · linarith
  exfalso
  have h2 : trSL (Cm U) = 2 := by linarith
  obtain ⟨M, hA0, hB0⟩ := exists_common_upper U h2
  set A₀ := M⁻¹ * A U * M
  set B₀ := M⁻¹ * B U * M
  have hC0 : M⁻¹ * Cm U * M = A₀⁻¹ * B₀⁻¹ * A₀ * B₀ := by simp only [A₀, B₀, Cm]; group
  have hC : Unipotent (M⁻¹ * Cm U * M) := by rw [hC0]; exact commutator_unipotent hA0 hB0
  have hτ : (M⁻¹ * Cm U * M) 0 1 ≠ 0 := by
    intro hτ
    have h1 : M⁻¹ * Cm U * M = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hC.1, hC.2.1, hC.2.2, hτ]
    have h2 : Cm U = 1 := by
      have := congrArg (fun g ↦ M * g * M⁻¹) h1
      rw [show M * (M⁻¹ * Cm U * M) * M⁻¹ = Cm U by group] at this
      simpa using this
    exact Cm_smul_ne U UpperHalfPlane.I (by rw [h2, one_smul])
  -- the upper left entries
  have hdetA : A₀ 0 0 * A₀ 1 1 = 1 := by have := det_SL A₀; rw [hA0] at this; linarith
  have hdetB : B₀ 0 0 * B₀ 1 1 = 1 := by have := det_SL B₀; rw [hB0] at this; linarith
  have case_lt : ∀ {X : SL(2, ℝ)}, X ∈ U.deckGroup → (M⁻¹ * X * M) 1 0 = 0 →
      (M⁻¹ * X * M) 0 0 * (M⁻¹ * X * M) 1 1 = 1 → |(M⁻¹ * X * M) 0 0| ≠ 1 → False := by
    intro X hX hX0 hdet hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact no_accumulation U hX hX0 hlt hC hτ
    · have hinv : M⁻¹ * X⁻¹ * M = (M⁻¹ * X * M)⁻¹ := by group
      refine no_accumulation U (X := X⁻¹) (inv_mem hX) ?_ ?_ hC hτ
      · rw [hinv, inv_apply_one_zero, hX0, neg_zero]
      · rw [hinv, inv_apply_zero_zero]
        have h1 : (M⁻¹ * X * M) 1 1 = ((M⁻¹ * X * M) 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
        rw [h1, abs_inv]
        exact inv_lt_one_of_one_lt₀ hgt
  by_cases hα : |A₀ 0 0| = 1
  · by_cases hβ : |B₀ 0 0| = 1
    · -- `A₀`, `B₀` are `±` unipotent, so they commute and `C = 1`
      have hα2 : A₀ 1 1 = A₀ 0 0 := by
        have hsq : A₀ 0 0 ^ 2 = 1 := by rw [← sq_abs, hα, one_pow]
        linear_combination (-(A₀ 1 1)) * hsq + (A₀ 0 0) * hdetA
      have hβ2 : B₀ 1 1 = B₀ 0 0 := by
        have hsq : B₀ 0 0 ^ 2 = 1 := by rw [← sq_abs, hβ, one_pow]
        linear_combination (-(B₀ 1 1)) * hsq + (B₀ 0 0) * hdetB
      apply hτ
      rw [hC0]
      simp only [mul_apply_SL, inv_apply_zero_zero, inv_apply_one_zero, inv_apply_one_one,
        inv_apply_zero_one, hA0, hB0, hα2, hβ2]
      rw [hα2] at hdetA; rw [hβ2] at hdetB
      ring_nf
    · exact case_lt (B_mem U) hB0 hdetB hβ
  · exact case_lt (A_mem U) hA0 hdetA hα

/-- The commutator of the edge pairings has trace `-2` in the order used for U1. -/
theorem trace_commutator :
    Matrix.trace ((A U * B U * (A U)⁻¹ * (B U)⁻¹ : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) = -2 := by
  rw [← trSL_eq_trace, mul_assoc (A U * B U) (A U)⁻¹ (B U)⁻¹,
    trSL_mul_comm (A U * B U)]
  simpa only [Cm, mul_assoc] using trace_Cm U

/-- The first edge pairing has nonzero matrix trace. -/
theorem trace_A_ne_zero : Matrix.trace (A U : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  rw [← trSL_eq_trace]
  exact trSL_A_ne_zero U

end Peripheral

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic
