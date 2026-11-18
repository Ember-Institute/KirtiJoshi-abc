/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Mathlib.RingTheory.Ideal.GoingUp

namespace AbcAdaptation.Tripod
open AbcAdaptation.Reference.Iut
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The prime of `𝓞 k` below a finite place of `K`. -/
noncomputable def primeUnder (w : FinitePlace K) : HeightOneSpectrum (𝓞 k) where
  asIdeal := w.maximalIdeal.asIdeal.comap (algebraMap (𝓞 k) (𝓞 K))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.maximalIdeal.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

/-- The finite place of `k` below a finite place of `K`. -/
noncomputable def placeUnder (w : FinitePlace K) : FinitePlace k :=
  FinitePlace.mk (primeUnder w)

lemma placeUnder_maximalIdeal (w : FinitePlace K) :
    (placeUnder (k := k) w).maximalIdeal.asIdeal =
      w.maximalIdeal.asIdeal.comap (algebraMap (𝓞 k) (𝓞 K)) := by
  rw [placeUnder, FinitePlace.maximalIdeal_mk]
  rfl

/-- `w` lies over the place below it. -/
lemma liesOver_placeUnder (w : FinitePlace K) : FinitePlace.LiesOver w (placeUnder (k := k) w) :=
  ⟨by rw [placeUnder_maximalIdeal]⟩

/-- The place below is unique. -/
lemma placeUnder_eq_of_liesOver_place {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : placeUnder w = v := by
  symm
  apply (FinitePlace.maximalIdeal_inj _ _).mp
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [placeUnder_maximalIdeal]
  exact hwv.over

end AbcAdaptation.Tripod
