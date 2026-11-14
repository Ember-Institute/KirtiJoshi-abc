import Lean
import Definitions.Def_FermatBelyiConductorExtensionFinitePlaces
import Definitions.Def_FermatBelyiConductorExtensionChildren

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Multiplicity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

lemma finiteMultiplicity_of_isPrime {P I : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥) :
    FiniteMultiplicity P I :=
  FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP inferInstance) hI

/-- `P^n ∣ I ↔ n ≤ ord_P(I)` for a nonzero prime `P` and `I ≠ 0`. -/
lemma pow_dvd_iff_le_multiplicity {P I : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥)
    {n : ℕ} : P ^ n ∣ I ↔ n ≤ multiplicity P I :=
  (finiteMultiplicity_of_isPrime hP hI).pow_dvd_iff_le_multiplicity

end Multiplicity

section Prime

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) (P : Ideal (𝓞 L)) [P.IsPrime]
  [P.LiesOver 𝔭]

include h𝔭

omit [NumberField F] [NumberField L] [𝔭.IsMaximal] [P.IsPrime] in
lemma ne_bot_of_liesOver : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P

omit [P.IsPrime] in
/-- `log N(P) = f(P|𝔭)·log N(𝔭)`. -/
lemma log_absNorm_eq_inertiaDeg_mul :
    Real.log (Ideal.absNorm P) = 𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭 inferInstance h𝔭, Nat.cast_pow,
    Real.log_pow]

omit h𝔭 [NumberField F] [𝔭.IsMaximal] [P.IsPrime] [P.LiesOver 𝔭] in
lemma pow_ramificationIdx'_dvd :
    P ^ 𝔭.ramificationIdx' P ∣ 𝔭.map (algebraMap (𝓞 F) (𝓞 L)) :=
  Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'

/-- **(a)** `e(P|𝔭) − 1 ≤ ord_P(𝔇)`. -/
lemma ramificationIdx'_sub_one_le_multiplicity :
    𝔭.ramificationIdx' P - 1 ≤ multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) :=
  (pow_dvd_iff_le_multiplicity (ne_bot_of_liesOver h𝔭 P) differentIdeal_ne_bot).mp
    (pow_sub_one_dvd_differentIdeal (𝓞 F) P _ h𝔭 (pow_ramificationIdx'_dvd P))

end Prime

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal]

/-- The summands of `diffContrib` in terms of `ord_P(𝔇)` and `f(P|𝔭)`. -/
lemma diffContrib_eq (h𝔭 : 𝔭 ≠ ⊥) :
    diffContrib L 𝔭 = ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
      (multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) : ℝ) * 𝔭.inertiaDeg' P *
        Real.log (Ideal.absNorm 𝔭) / finrank ℚ L := by
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  rw [log_absNorm_eq_inertiaDeg_mul h𝔭 P, mul_assoc]

/-- **(a) The lower bound**: `∑_{P ∣ 𝔭} (e − 1)·f·log N(𝔭)/[L : ℚ] ≤ diffContrib L 𝔭`. -/
theorem sum_le_diffContrib (h𝔭 : 𝔭 ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
      ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) * 𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) /
        finrank ℚ L ≤ diffContrib L 𝔭 := by
  rw [diffContrib_eq h𝔭]
  refine Finset.sum_le_sum fun P hP => ?_
  obtain ⟨hPp, hPl⟩ := (mem_primesOverFinset_iff' h𝔭).mp hP
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ?_ (by positivity)) (Real.log_natCast_nonneg _)) (by positivity)
  exact_mod_cast ramificationIdx'_sub_one_le_multiplicity h𝔭 P

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/-- `log N(w) = f·log N(u)` for `w` over `u`. -/
lemma log_placeNorm_eq {w : FinitePlace L} {u : FinitePlace F} (h : PlaceLiesOver w u) :
    Real.log (placeNorm w) = placeInertiaDeg w u * Real.log (placeNorm u) := by
  rw [placeNorm_eq_pow h, Nat.cast_pow, Real.log_pow]

/-- The finite place of `L` of a prime of `𝓞 L` over `𝔭_u`. -/
noncomputable def placeOfPrimeOver (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) : FinitePlace L :=
  haveI := u.maximalIdeal.isMaximal
  FinitePlace.mk
    ⟨P, ((mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP).1, by
      obtain ⟨_, _⟩ := (mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP
      exact Ideal.ne_bot_of_liesOver_of_ne_bot u.maximalIdeal.ne_bot P⟩

lemma placeOfPrimeOver_maximalIdeal (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) :
    (placeOfPrimeOver u hP).maximalIdeal.asIdeal = P := by
  rw [placeOfPrimeOver, FinitePlace.maximalIdeal_mk]

lemma placeLiesOver_placeOfPrimeOver (u : FinitePlace F) {P : Ideal (𝓞 L)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L)) :
    PlaceLiesOver (placeOfPrimeOver u hP) u := by
  haveI := u.maximalIdeal.isMaximal
  unfold PlaceLiesOver
  rw [placeOfPrimeOver_maximalIdeal]
  exact ((mem_primesOverFinset_iff' u.maximalIdeal.ne_bot).mp hP).2

/-- **The places over `u` correspond to `primesOverFinset`**: a sum over the places of `L`
over `u` of a function of the prime is the sum over the primes of `𝓞 L` over `𝔭_u`. -/
theorem sum_placesOver_eq {M : Type*} [AddCommMonoid M] (u : FinitePlace F)
    (g : Ideal (𝓞 L) → M) :
    ∑ w ∈ placesOver L u, g w.maximalIdeal.asIdeal =
      ∑ P ∈ IsDedekindDomain.primesOverFinset u.maximalIdeal.asIdeal (𝓞 L), g P := by
  refine Finset.sum_bij (fun w _ => w.maximalIdeal.asIdeal)
    (fun w hw => mem_primesOverFinset_of_placeLiesOver (mem_placesOver.mp hw)) ?_ ?_
    (fun _ _ => rfl)
  · intro w₁ _ w₂ _ h
    exact (FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h)
  · intro P hP
    exact ⟨placeOfPrimeOver u hP, mem_placesOver.mpr (placeLiesOver_placeOfPrimeOver u hP),
      placeOfPrimeOver_maximalIdeal u hP⟩

/-- `∑_{w ∣ u} e(w|u)·f(w|u) = [L : F]`. -/
theorem sum_placesOver_mul_eq_finrank (u : FinitePlace F) :
    ∑ w ∈ placesOver L u, placeRamIdx w u * placeInertiaDeg w u = finrank F L := by
  haveI := u.maximalIdeal.isMaximal
  rw [sum_placesOver_eq u (fun P => u.maximalIdeal.asIdeal.ramificationIdx' P *
    u.maximalIdeal.asIdeal.inertiaDeg' P)]
  exact Ideal.sum_ramification_inertia (𝓞 L) F L u.maximalIdeal.ne_bot

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

lemma finrank_ℚ_pos (K : Type*) [Field K] [NumberField K] : (0 : ℝ) < finrank ℚ K := by
  exact_mod_cast finrank_pos

section Local

variable {F : Type*} [Field F] [NumberField F] (L : Type*) [Field L] [NumberField L]
  [Algebra F L]

/-- **The local comparison at a place `u` of `F`**:
`log N(u)/[F : ℚ] ≤ ∑_{w ∣ u} log N(w)/[L : ℚ] + diffContrib L u`. -/
theorem log_placeNorm_div_le (u : FinitePlace F) :
    Real.log (placeNorm u) / finrank ℚ F ≤
      ∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L +
        diffContrib L u.maximalIdeal.asIdeal := by
  haveI := u.maximalIdeal.isMaximal
  set 𝔭 := u.maximalIdeal.asIdeal
  have hsum := sum_placesOver_mul_eq_finrank (L := L) u
  have hF := finrank_ℚ_pos F
  have hFL : (0 : ℝ) < finrank F L := by exact_mod_cast finrank_pos
  calc Real.log (placeNorm u) / finrank ℚ F
      = ∑ w ∈ placesOver L u, ((placeRamIdx w u * placeInertiaDeg w u : ℕ) : ℝ) *
          (Real.log (placeNorm u) / finrank ℚ L) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, hsum, ← finrank_mul_finrank ℚ F L, Nat.cast_mul]
        field_simp
    _ = ∑ w ∈ placesOver L u, (Real.log (placeNorm w) / finrank ℚ L +
          ((𝔭.ramificationIdx' w.maximalIdeal.asIdeal - 1 : ℕ) : ℝ) *
            𝔭.inertiaDeg' w.maximalIdeal.asIdeal * Real.log (Ideal.absNorm 𝔭) /
              finrank ℚ L) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have h := mem_placesOver.mp hw
        have he : 1 ≤ placeRamIdx w u := Nat.one_le_iff_ne_zero.mpr (placeRamIdx_ne_zero h)
        rw [log_placeNorm_eq h, Nat.cast_sub he]
        simp only [placeRamIdx, placeInertiaDeg, placeNorm, Nat.cast_mul, Nat.cast_one]
        ring
    _ = ∑ w ∈ placesOver L u, Real.log (placeNorm w) / finrank ℚ L +
          ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 L),
            ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) * 𝔭.inertiaDeg' P *
              Real.log (Ideal.absNorm 𝔭) / finrank ℚ L := by
        rw [Finset.sum_add_distrib]
        congr 1
        exact sum_placesOver_eq u (fun P => ((𝔭.ramificationIdx' P - 1 : ℕ) : ℝ) *
          𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) / finrank ℚ L)
    _ ≤ _ := add_le_add le_rfl (sum_le_diffContrib u.maximalIdeal.ne_bot)

end Local

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/

set_option autoImplicit false
open NumberField
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Source Conductor.lean:104–136 on the unchanged actual image-field inclusion.
The source proof uses only the lower bound e−1 ≤ ord_P(different). -/
theorem closedLocalConductorSource : BelyiActualFieldLocalConductorComparison := by
  intro N M hRF φ x hgood
  letI : FiniteDimensional ℚ x.fieldOf := pointField_finiteDimensional M hRF x
  letI : Algebra (Tripod.fieldOf (belyiImage M φ x).1) x.fieldOf :=
    (IntermediateField.inclusion (belyiImage_field_le M φ x hgood)).toRingHom.toAlgebra
  intro u
  exact ConductorExtensionSource.log_placeNorm_div_le x.fieldOf u

end AbcAdaptation.Tripod.Fermat.Proper

open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

theorem solution : BelyiActualFieldLocalConductorComparison := closedLocalConductorSource

theorem PlatformOriginalTargetType : BelyiActualFieldLocalConductorComparison := solution

theorem PlatformSourceTargetType : BelyiActualFieldLocalConductorComparison := solution

open Lean
run_meta do
  let original ← getConstInfo `PlatformOriginalTargetType
  let current ← getConstInfo `PlatformSourceTargetType
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq original.type proof.type do throwError "Original platform type differs"
  unless ← Meta.isDefEq current.type proof.type do throwError "Current wrapper type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Unexpected direct-proof axiom {ax}"
  IO.FS.writeFile ".local/adaptation/local-conductor-sourceproof-20261115/solution-type-axioms.json" (Json.pretty (Json.mkObj [
    ("original_type_equal",Json.bool true),("source_type_equal",Json.bool true),
    ("type",Json.str (← Meta.ppExpr proof.type).pretty),("axioms",toJson (axs.map toString))]))
