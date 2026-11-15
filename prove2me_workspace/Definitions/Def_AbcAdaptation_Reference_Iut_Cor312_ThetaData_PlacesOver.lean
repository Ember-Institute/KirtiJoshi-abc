/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: Iut/Cor312/ThetaData/PlacesOver.lean
Original authors: The iut contributors
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original license: Apache-2.0; the original copyright and license notice is retained below.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# Places of number fields over places of subfields (taxis #1529, #1494)

For number fields `k ⊆ K`:

* `Iut.FinitePlace.exists_liesOver`: every finite place of `k` has a finite place of `K`
  over it (going up for the integral extension `𝓞_k ⊆ 𝓞_K`);
* `Iut.InfinitePlace.exists_liesOver`: every infinite place of `k` has an infinite place of
  `K` over it (extension of complex embeddings);
* `Iut.galPlace σ w`: the action of `σ ∈ Gal(K/k)` on the finite places of `K`
  (`σ·𝔓 = σ(𝔓)`, through the restriction of `σ` to `𝓞_K`), which preserves the place of
  `k` below (`Iut.galPlace_liesOver`);
* `Iut.decompGroup w`: the **decomposition group** of a finite place `w` of `K` in
  `Gal(F̄/K)` — the stabilizer of a prime of the integral closure of `𝓞_K` in `F̄` lying
  over `𝔓_w` — and its closedness in the Krull topology (`Iut.decompGroup_isClosed`).
-/

namespace Iut

open NumberField IsDedekindDomain

section Places

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- A number field is algebraic over any subfield (for any algebra structure). -/
instance numberField_isAlgebraic : Algebra.IsAlgebraic k K := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  constructor
  intro x
  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x
  refine ⟨p.map (algebraMap ℚ k), (Polynomial.map_ne_zero_iff (algebraMap ℚ k).injective).mpr hp0,
    ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    Subsingleton.elim ((algebraMap k K).comp (algebraMap ℚ k)) (algebraMap ℚ K),
    ← Polynomial.aeval_def, hpx]

/-! ### The Galois action on finite places -/

/-- The restriction of `σ ∈ Gal(K/k)` to the rings of integers. -/
noncomputable def galRestrictInt (σ : K ≃ₐ[k] K) : 𝓞 K ≃ₐ[𝓞 k] 𝓞 K :=
  galRestrict (𝓞 k) k K (𝓞 K) σ

lemma coe_galRestrictInt (σ : K ≃ₐ[k] K) (x : 𝓞 K) :
    (galRestrictInt σ x : K) = σ (x : K) :=
  algebraMap_galRestrict_apply (A := 𝓞 k) (K := k) (L := K) (B := 𝓞 K) σ x

/-- **The action of `Gal(K/k)` on the finite places of `K`**: `σ·w` is the place of the
prime `σ(𝔓_w) = (σ⁻¹)⁻¹(𝔓_w)`. -/
noncomputable def galPlace (σ : K ≃ₐ[k] K) (w : FinitePlace K) : FinitePlace K :=
  FinitePlace.mk (HeightOneSpectrum.comap (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K)
    (galRestrictInt σ⁻¹).surjective w.maximalIdeal)

lemma galPlace_maximalIdeal (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    (galPlace σ w).maximalIdeal.asIdeal =
      w.maximalIdeal.asIdeal.comap (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K) := by
  unfold galPlace
  rw [FinitePlace.maximalIdeal_mk]
  rfl

/-- **The action preserves the place below**, for places of any subfield `k₀ ⊆ k` (with
the algebra structure of `K` over `k₀` factoring through `k`). -/
theorem galPlace_liesOver {k₀ : Type*} [Field k₀] [NumberField k₀] [Algebra k₀ k] [Algebra k₀ K]
    (halg : ∀ x : k₀, algebraMap k₀ K x = algebraMap k K (algebraMap k₀ k x))
    (σ : K ≃ₐ[k] K) {w : FinitePlace K} {v : FinitePlace k₀}
    (hw : FinitePlace.LiesOver w v) : FinitePlace.LiesOver (galPlace σ w) v := by
  unfold FinitePlace.LiesOver at hw ⊢
  refine ⟨?_⟩
  rw [hw.over, galPlace_maximalIdeal, Ideal.under_def, Ideal.under_def, Ideal.comap_comap]
  congr 1
  ext x
  rw [RingHom.comp_apply, RingHom.coe_coe, coe_galRestrictInt]
  have h : (algebraMap (𝓞 k₀) (𝓞 K) x : K) = algebraMap k K (algebraMap k₀ k (x : k₀)) := by
    rw [← halg]
    change algebraMap (𝓞 K) K (algebraMap (𝓞 k₀) (𝓞 K) x) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 k₀) (𝓞 K) K,
      IsScalarTower.algebraMap_apply (𝓞 k₀) k₀ K]
  rw [h, AlgEquiv.commutes]

/-! ### Decomposition groups -/

variable (K) (Fbar : Type*) [Field Fbar] [Algebra K Fbar]

end Places

end Iut

end AbcAdaptation.Reference
