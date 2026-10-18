/-
original-paths: refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean,
  refer/iut/Iut/Concrete/LocalConstruct/LogShell.lean,
  refer/iut/Iut/Concrete/LocalConstruct/Arithmetic.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commits: PadicLog bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c,
  LogShell fe96f99cae5c6d48d25113163f1b9b388fc35814,
  Arithmetic b76207ab8955e68a7408d5d2a770b75a30c3bebf
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: use actual completion carrier, existing valuation of the residue
  characteristic, and local log-shell; retain ramification support via the
  nonzero different ideal. No reference LocalTheory or assumption imported.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegree
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogBall

/-!
source-id: JT-SCENE1-LOCAL-UNRAMIFIED-LOG-SHELL
source: reference PadicLog logShell_subset_closedBall / logShell_eq_closedBall,
LogShell factorLogShell_eq_of_unramified, Arithmetic ramified_finite;
IUT I Definition 5.4.5 and IUT IV Proposition 1.2.
fidelity: derives the actual uniformizer norm condition from e=1; at odd
unramified places the ordinary 2p-normalized shell is the integral ball.
Proves only finitely many actual places have e!=1 by the different ideal.
No global paper theta/BK identity is asserted.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField IsDedekindDomain
open JoshiTeich.Prologue.Arithmetic
open scoped Valued
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K]

local instance unramifiedCharZero (w : FinitePlace K) : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective

theorem norm_le_prime_of_norm_lt_one_of_unramified (w : FinitePlace K)
    (he : ramIdx w = 1) (a : completionAt K w) (ha : ‖a‖ < 1) :
    ‖a‖ ≤ ‖(residueChar w : completionAt K w)‖ := by
  have hvp : Valued.v (residueChar w : completionAt K w) = WithZero.exp (-1 : ℤ) := by
    have h := valued_residueChar w
    rw [he, Nat.cast_one] at h
    rwa [map_natCast] at h
  rw [Valued.toNormedField.norm_le_iff, hvp]
  rw [Valued.toNormedField.norm_lt_one_iff] at ha
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [map_zero]; exact bot_le
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v a = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 ha0)).symm⟩
    rw [hm] at ha ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    rw [WithZero.exp_le_exp]
    omega

theorem logShell_eq_closedBall_of_unramified (w : FinitePlace K)
    (hodd : Odd (residueChar w)) (he : ramIdx w = 1) :
    LocalPadicLog.logShell (k := completionAt K w) (residueChar w) =
      Metric.closedBall (0 : completionAt K w) 1 := by
  have hp := residueChar_prime w
  have hpk : ‖(residueChar w : completionAt K w)‖ < 1 := by
    have h := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
    rwa [← FinitePlace.embedding_apply, map_natCast] at h
  apply Set.Subset.antisymm _ (LocalPadicLog.closedBall_subset_logShell hp hpk)
  rintro y ⟨a, ha, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv, norm_mul,
    LocalPadicLog.norm_two_eq_one hp hpk hodd, one_mul]
  have hp0 : 0 < ‖(residueChar w : completionAt K w)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [← div_eq_inv_mul, div_le_one hp0]
  exact LocalPadicLog.norm_padicLog_le_norm_p hp hpk
    (norm_le_prime_of_norm_lt_one_of_unramified w he _ ha)

attribute [local instance] FractionRing.liftAlgebra

theorem dvd_differentIdeal_of_ramIdx_ne_one (w : FinitePlace K) (he : ramIdx w ≠ 1) :
    w.maximalIdeal.asIdeal ∣ _root_.differentIdeal ℤ (𝓞 K) := by
  rw [dvd_differentIdeal_iff]
  intro hunr
  exact he (Ideal.ramificationIdx_eq_one w.maximalIdeal.asIdeal ℤ)

theorem ramified_finite : {w : FinitePlace K | ramIdx w ≠ 1}.Finite := by
  have hD : _root_.differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : ((UniqueFactorizationMonoid.normalizedFactors
      (_root_.differentIdeal ℤ (𝓞 K))).toFinset : Set (Ideal (𝓞 K))).Finite := Finset.finite_toSet _
  refine (hfin.preimage (f := fun w : FinitePlace K => w.maximalIdeal.asIdeal) ?_).subset ?_
  · intro w₁ _ w₂ _ h
    exact FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h)
  · intro w hw
    rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hD]
    exact ⟨inferInstance, Ideal.le_of_dvd (dvd_differentIdeal_of_ramIdx_ne_one w hw)⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion
