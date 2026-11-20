/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Rational.lean, lines 186–241
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiRational
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.RatCert

open Asymptotics Bornology Filter Polynomial Set
open scoped Topology

variable {f N D H K R : ℂ[X]} {c : ℂ} (hc : RatCert f N D H K R c)

/-- At a root of the cubic, the norm of the certified rational function tends to infinity. -/
theorem tendsto_nhdsNE {z : ℂ} (hz : f.eval z = 0) :
    Tendsto hc.G (𝓝[≠] z) (cobounded ℂ) := by
  have hN := hc.N_eval_ne hz
  have hD := (hc.D_eval_eq_zero_iff z).mpr hz
  have hDne : ∀ᶠ y in 𝓝[≠] z, D.eval y ≠ 0 := by
    have hclosed : IsClosed ({y | D.IsRoot y} \ {z}) :=
      (Polynomial.finite_setOfPred_isRoot hc.D_ne).sdiff.isClosed
    have hnear : ∀ᶠ y in 𝓝[≠] z, y ∉ {y | D.IsRoot y} \ {z} :=
      nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds (by simp))
    filter_upwards [hnear, self_mem_nhdsWithin] with y hy hyz
    exact fun h ↦ hy ⟨h, hyz⟩
  have hDt : Tendsto (fun y ↦ D.eval y) (𝓝[≠] z) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hDne⟩
    rw [← hD]
    exact (D.continuous.tendsto z).mono_left nhdsWithin_le_nhds
  have hinv := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp hDt
  rw [← tendsto_norm_atTop_iff_cobounded] at hinv ⊢
  have hNt : Tendsto (fun y ↦ ‖N.eval y‖) (𝓝[≠] z) (𝓝 ‖N.eval z‖) :=
    ((N.continuous.tendsto z).mono_left nhdsWithin_le_nhds).norm
  exact ((hNt.pos_mul_atTop (norm_pos_iff.mpr hN) hinv).congr fun y ↦
    by simp only [Function.comp, G_def, div_eq_mul_inv, norm_mul])

/-- The certified rational function has a pole at infinity. -/
theorem tendsto_cobounded : Tendsto hc.G (cobounded ℂ) (cobounded ℂ) := by
  have hN0 : N ≠ 0 := by
    intro h
    have hd := hc.deg
    rw [h, natDegree_zero] at hd
    exact Nat.not_lt_zero _ hd
  have heN := isEquivalent_cobounded_leading_monomial (P := N)
  have heD := isEquivalent_cobounded_leading_monomial (P := D)
  obtain ⟨φ, hφ, hGφ⟩ := (heN.div heD).exists_eq_mul
  set k := N.natDegree - D.natDegree
  have hk : 0 < k := Nat.sub_pos_of_lt hc.deg
  have hlN := leadingCoeff_ne_zero.mpr hN0
  have hlD := leadingCoeff_ne_zero.mpr hc.D_ne
  have hmon : ∀ᶠ x in cobounded ℂ, (N.leadingCoeff * x ^ N.natDegree) /
      (D.leadingCoeff * x ^ D.natDegree) = N.leadingCoeff / D.leadingCoeff * x ^ k := by
    filter_upwards [eventually_ne_cobounded (0 : ℂ)] with x hx
    have hpow : x ^ N.natDegree = x ^ k * x ^ D.natDegree := by
      rw [← pow_add, Nat.sub_add_cancel hc.deg.le]
    rw [hpow]
    field_simp
  have hmt : Tendsto (fun x : ℂ ↦ ‖N.leadingCoeff / D.leadingCoeff * x ^ k‖)
      (cobounded ℂ) atTop := by
    simp only [norm_mul, norm_pow]
    exact ((tendsto_pow_atTop hk.ne').comp tendsto_norm_cobounded_atTop).const_mul_atTop
      (norm_pos_iff.mpr (div_ne_zero hlN hlD))
  have hφt : Tendsto (fun x ↦ ‖φ x‖) (cobounded ℂ) (𝓝 1) := by
    simpa using hφ.norm
  rw [← tendsto_norm_atTop_iff_cobounded]
  refine (hφt.pos_mul_atTop one_pos hmt).congr' ?_
  filter_upwards [hGφ, hmon] with x hx hx'
  simp only [Pi.mul_apply, Pi.div_apply] at hx
  simp only [G_def, hx, hx', norm_mul]

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi.RatCert
