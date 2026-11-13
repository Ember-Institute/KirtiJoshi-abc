/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation and extraction of pinned Belyi source proofs.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source: Belyi/CurveDeriv/Basic.lean; SHA-256: cf1b11adab96fbd7d7bb5114e7215dcbf8b8cda1a8eda573e9759ac5316f40b2.
Source: Belyi/CurveDeriv/Local.lean; SHA-256: cb930e45cba81a1377ab8281264d938868ae7834d32c480a9af9d29012eb1aae.
-/
import Definitions.Def_FermatCurveDerivationBasic
import Mathlib.RingTheory.Valuation.ValuationSubring

set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

section Extension

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

open KaehlerDifferential TensorProduct

@[simp]
theorem extendOfFormallyEtale_algebraMap [Algebra.FormallyEtale S T]
    (d : Derivation R S T) (s : S) :
    extendOfFormallyEtale d (algebraMap S T s) = d s := by
  simp [extendOfFormallyEtale, tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

end Extension

variable {K : Type*} [Field K] [CharZero K]

variable (t : K) in
theorem polyDeriv_apply (ht : Transcendental ℚ t) (p : ℚ[X]) :
    polyDeriv t ht (Polynomial.algEquivOfTranscendental ℚ t ht p) = aeval t (derivative p) := by
  simp only [polyDeriv, Derivation.mk_coe, LinearMap.coe_mk, AddHom.coe_mk,
    AlgEquiv.symm_apply_apply]

variable {t : K}

theorem derivAlong_aeval (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] (p : ℚ[X]) :
    derivAlong t (aeval t p) = aeval t (derivative p) := by
  have := formallyEtale_adjoin t
  have key : aeval t p = algebraMap (Algebra.adjoin ℚ {t}) K
      (Polynomial.algEquivOfTranscendental ℚ t ht p) :=
    (coe_algEquivOfTranscendental t ht p).symm
  rw [derivAlong, dif_pos ⟨ht, ‹_›⟩, key, extendOfFormallyEtale_algebraMap,
    polyDeriv_apply]

variable {O : ValuationSubring K}

theorem aeval_mem (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K} (hx : x ∈ O) (p : ℚ[X]) :
    aeval x p ∈ O := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hQ _) (pow_mem hx _)

variable {π : K}

theorem mem_of_mem_adjoin (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O) {x : K}
    (hx : x ∈ Algebra.adjoin ℚ {π}) : x ∈ O := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, rfl⟩ := hx
  exact aeval_mem hQ hπO p

variable (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O)
include ht hQ hπO

/-- Source polynomial-adjoin derivative membership lemma. -/
theorem derivAlong_mem_of_mem_adjoin {a : K} (ha : a ∈ Algebra.adjoin ℚ {π}) :
    derivAlong π a ∈ O := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨p, rfl⟩ := ha
  change derivAlong π (aeval π p) ∈ O
  rw [derivAlong_aeval ht]
  exact aeval_mem hQ hπO _

end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv
