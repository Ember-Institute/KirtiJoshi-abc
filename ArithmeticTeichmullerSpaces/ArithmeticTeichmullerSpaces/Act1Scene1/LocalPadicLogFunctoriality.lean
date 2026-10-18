/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/LogShell.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: fe96f99cae5c6d48d25113163f1b9b388fc35814
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt continuous endomorphism/principal-unit/logarithm proofs
  to the independent LocalPadicLog definitions and actual 2p normalization.
  No reference LocalTheory, factor quotient or assumed stability imported.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLog

/-!
source-id: JT-SCENE1-LOCAL-PADIC-LOG-FUNCTORIALITY
source: reference LocalConstruct/LogShell (64--115); IUT IV Proposition 1.2
and Joshi III log-shells for the intended invariance consumer.
fidelity: continuous ring endomorphisms preserve principal units, commute
with the convergent ordinary logarithm, and map the 2p-normalized log-shell
into itself. No norm isometry or BK-log identification is assumed.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog

open Filter Topology
open scoped Valued
universe u
noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] in
theorem norm_lt_one_iff_tendsto_pow {F : Type*} [NormedField F] (a : F) :
    ‖a‖ < 1 ↔ Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  refine ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one, fun h => ?_⟩
  by_contra hle
  push Not at hle
  rw [NormedAddGroup.tendsto_nhds_zero] at h
  obtain ⟨n, hn⟩ := (h 1 one_pos).exists
  rw [norm_pow] at hn
  exact absurd hn (not_lt.mpr (one_le_pow₀ hle))

theorem norm_map_sub_one_lt (τ : k →+* k) (hτ : Continuous τ)
    {u : k} (hu : ‖u - 1‖ < 1) : ‖τ u - 1‖ < 1 := by
  rw [norm_lt_one_iff_tendsto_pow] at hu ⊢
  have h := (hτ.tendsto 0).comp hu
  rw [map_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, map_pow, map_sub, map_one]

variable [CompleteSpace k] [CharZero k] {p : ℕ}

theorem map_padicLog (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (τ : k →+* k) (hτ : Continuous τ) {u : k} (hu : ‖u - 1‖ < 1) :
    τ (padicLog u) = padicLog (τ u) := by
  have h := (hasSum_padicLog hp hpk hu).map τ hτ
  have hterm : (⇑τ ∘ logTerm u) = logTerm (τ u) := by
    funext n
    simp only [Function.comp_apply, logTerm, map_div₀, map_mul, map_pow, map_neg, map_one,
      map_sub, map_add, map_natCast]
  rw [hterm] at h
  exact h.tsum_eq.symm

theorem image_logShell_subset (hp : p.Prime) (hpk : ‖(p : k)‖ < 1)
    (τ : k →+* k) (hτ : Continuous τ) : τ '' logShell (k := k) p ⊆ logShell p := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨τ u, norm_map_sub_one_lt τ hτ hu, ?_⟩
  rw [map_mul, map_inv₀, map_mul, map_ofNat, map_natCast, map_padicLog hp hpk τ hτ hu]

end
end JoshiTeich.Act1Scene1.LocalPadicLog
