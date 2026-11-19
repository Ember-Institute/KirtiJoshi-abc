/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 2d8f000457da6447fa4df4bfec7365c1a49b6384
Original paths Iut/Tripod/WildRamIdx.lean and Iut/Tripod/TpdInertia.lean
-/
import Solutions.Source_TripodTpdInertia
import Mathlib.Algebra.Group.Prod

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable (P : CurveProviders) (x : Pt)

/-- The relative degree divides `2³ · |GL₂(𝔽₃)| · |GL₂(𝔽₅)| = 184320`. -/
theorem finrank_tpd_dvd : Module.finrank (tpd P x) (P.curve x).F ∣ 184320 := by
  letI : IsGalois (tpd P x) (P.curve x).F := isGalois_tpd_curve' (P := P) (x := x)
  letI : FiniteDimensional (tpd P x) (P.curve x).F :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hi : ∃ a : tpd P x, (sqrtNegOne' P x) ^ 2 = algebraMap (tpd P x) (P.curve x).F a :=
    ⟨-1, by rw [map_neg, map_one, sqrtNegOne'_sq]⟩
  have hi0 : sqrtNegOne' P x ≠ 0 := by
    intro h
    have hsq := sqrtNegOne'_sq P x
    rw [h, zero_pow two_ne_zero] at hsq
    exact neg_ne_zero.mpr one_ne_zero hsq.symm
  let εi := signHom (sqrtNegOne' P x) hi hi0
  let εa := signHom (sqrtLam' P x) (sqrtLam'_sq_mem P x) (sqrtLam'_ne_zero P x)
  let εb :=
    signHom (sqrtOneSubLam' P x) (sqrtOneSubLam'_sq_mem P x) (sqrtOneSubLam'_ne_zero P x)
  have hsub3 := torsionCoords_three_subset_fieldOf' x.1
  have hsub5 := torsionCoords_five_subset_fieldOf' x.1
  let ρ₃ := repF P x 3 hsub3
  let ρ₅ := repF P x 5 hsub5
  let ρ := εi.prod (εa.prod (εb.prod (ρ₃.prod ρ₅)))
  have hρ : Function.Injective ρ := by
    apply (injective_iff_map_eq_one ρ).mpr
    intro σ hσ
    change (εi σ, εa σ, εb σ, ρ₃ σ, ρ₅ σ) = (1, 1, 1, 1, 1) at hσ
    simp only [Prod.mk.injEq] at hσ
    obtain ⟨hσi, hσa, hσb, hσ3, hσ5⟩ := hσ
    have hfix3 := (mem_repF_ker_iff P x 3 hsub3 σ).mp (MonoidHom.mem_ker.mpr hσ3)
    have hfix5 := (mem_repF_ker_iff P x 5 hsub5 σ).mp (MonoidHom.mem_ker.mpr hσ5)
    refine algEquiv_eq_one_of_fixed (adjoin_tpdGens P x) σ fun c hc => ?_
    rcases hc with (hc | hc) | hc
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl
      · exact (signHom_eq_one_iff hi hi0 σ).mp hσi
      · exact (signHom_eq_one_iff _ _ σ).mp hσa
      · exact (signHom_eq_one_iff _ _ σ).mp hσb
    · exact torsionCoord_fixed_of_galF P x 3 hsub3 σ hfix3 hc c.2
    · exact torsionCoord_fixed_of_galF P x 5 hsub5 σ hfix5 hc c.2
  have hZ : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hcard : Nat.card (ℤˣ × ℤˣ × ℤˣ × Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) ×
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) = 184320 := by
    simp only [Nat.card_prod, hZ, card_GL_two] <;> decide
  rw [← IsGalois.card_aut_eq_finrank (tpd P x) (P.curve x).F]
  simpa only [hcard] using Subgroup.card_dvd_of_injective ρ hρ

end AbcAdaptation.Tripod
