/-
original-path: `refer/iut/Iut/Concrete/LocalConstruct/Arithmetic.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `b76207ab8955e68a7408d5d2a770b75a30c3bebf`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: adapt only the residue-characteristic valuation proofs to the
actual local arithmetic API; derive the completion norm and p-adic finrank
identities from the independently proved scalar algebraic-norm identity.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraNorm

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-DEGREE
fidelity: proves the actual completion dimension equals its arithmetic local
degree using the actual p-adic embedding. No compatible NormedSpace structure
for the raw completion norm is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField IsDedekindDomain WithZero
open JoshiTeich.Prologue.Arithmetic
open scoped Valued

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K]

theorem intValuation_residueChar (w : FinitePlace K) :
    w.maximalIdeal.intValuation (residueChar w : 𝓞 K) = exp (-(ramIdx w : ℤ)) := by
  have hp := residueChar_prime w
  have hp0 : (residueChar w : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hspan : Ideal.span {(residueChar w : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  have hmap : (Ideal.span {(residueChar w : ℤ)}).map (algebraMap ℤ (𝓞 K)) =
      Ideal.span {(residueChar w : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  haveI := residueChar_liesOver w
  have h : (Associates.mk w.maximalIdeal.asIdeal).count
      (Associates.mk (Ideal.span {(residueChar w : 𝓞 K)})).factors = ramIdx w := by
    rw [Ideal.count_associates_factors_eq hspan w.maximalIdeal.isPrime w.maximalIdeal.ne_bot]
    unfold ramIdx
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (Ideal.span {(residueChar w : ℤ)})
      w.maximalIdeal.asIdeal (by rw [hmap]; exact hspan), hmap]
  rw [w.maximalIdeal.intValuation_if_neg hp0, h]

theorem valued_residueChar (w : FinitePlace K) :
    Valued.v (algebraMap K (completionAt K w) (residueChar w : K)) =
      exp (-(ramIdx w : ℤ)) := by
  have h : algebraMap K (completionAt K w) (residueChar w : K) =
      FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (residueChar w : 𝓞 K)) := by
    rw [map_natCast (algebraMap (𝓞 K) K)]
    rfl
  rw [h, FinitePlace.embedding_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_residueChar]

theorem norm_residueChar_eq_inv_pow_localDeg (w : FinitePlace K) :
    ‖algebraMap K (completionAt K w) (residueChar w : K)‖ =
      (residueChar w : ℝ)⁻¹ ^ localDeg w := by
  rw [completionNorm_eq_residueChar_pow_of_valued w _ _ (valued_residueChar w),
    zpow_neg, zpow_natCast, ← pow_mul, ← inv_pow]
  rw [localDeg, Nat.mul_comm]

variable {p : ℕ} [Fact p.Prime]

theorem finrank_padic_eq_localDeg (w : FinitePlace K) (hw : residueChar w = p) :
    letI := padicAlgebra hw
    Module.finrank ℚ_[p] (completionAt K w) = localDeg w := by
  letI := padicAlgebra hw
  letI : Module.Finite ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  letI : CharZero (completionAt K w) :=
    charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
  have hcast : ((p : K) : completionAt K w) = (p : completionAt K w) :=
    map_natCast (FinitePlace.embedding w.maximalIdeal) p
  have hn := norm_algebraNorm_eq_completionNorm_of_contracting w hw
    ((p : K) : completionAt K w)
    (by rw [hcast]; exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (norm_natCast_prime_lt_one hw)
  rw [hcast, Algebra.norm_natCast, norm_pow, Padic.norm_p] at hn
  have ha := norm_residueChar_eq_inv_pow_localDeg w
  rw [hw, map_natCast] at ha
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact pow_right_injective₀ (inv_pos.mpr (lt_trans zero_lt_one hp1))
    (ne_of_lt (inv_lt_one_of_one_lt₀ hp1)) (hn.trans ha)

end
end JoshiTeich.Act1Scene1.LocalCompletion
