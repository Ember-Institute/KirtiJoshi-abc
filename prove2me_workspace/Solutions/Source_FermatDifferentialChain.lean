/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source proof from Belyi/CurveDeriv/Basic.lean:68-95,178-219,
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The proof closure already exists privately in the current regular-ramification
source theorem. Only the chain and reciprocal results become public here.
See this unit's validation receipts and source mappings.
-/
import Definitions.Def_FermatCurveDerivationAdjoin
import Mathlib.RingTheory.Unramified.Field

set_option autoImplicit false
open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


section Extension

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open KaehlerDifferential TensorProduct

omit [Algebra R S] [IsScalarTower R S T] in
private theorem eq_zero_of_formallyUnramified [Algebra.FormallyUnramified S T]
    (D : Derivation R T T) (hD : ∀ s : S, D (algebraMap S T s) = 0) : D = 0 := by
  let D' : Derivation S T T :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun s x => by
        rw [Algebra.smul_def, D.leibniz, hD, smul_zero, add_zero, smul_eq_mul, RingHom.id_apply,
          Algebra.smul_def]
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  ext x
  change D' x = 0
  rw [← D'.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D S T x) 0,
    map_zero]

omit [Algebra R S] [IsScalarTower R S T] in
private theorem ext_of_formallyUnramified [Algebra.FormallyUnramified S T]
    (D₁ D₂ : Derivation R T T) (h : ∀ s : S, D₁ (algebraMap S T s) = D₂ (algebraMap S T s)) :
    D₁ = D₂ := by
  rw [← sub_eq_zero]
  exact eq_zero_of_formallyUnramified (S := S) _ fun s => by simp [h s]

end Extension

variable {K : Type*} [Field K] [CharZero K] {t : K}

@[simp]
private theorem derivAlong_self (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t t = 1 := by
  simpa using derivAlong_aeval ht X

private theorem derivation_ext_of_eq (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K]
    (D₁ D₂ : Derivation ℚ K K) (h : D₁ t = D₂ t) : D₁ = D₂ := by
  have := formallyEtale_adjoin t
  refine ext_of_formallyUnramified (S := Algebra.adjoin ℚ {t}) D₁ D₂ fun s => ?_
  obtain ⟨p, hp⟩ := (Polynomial.algEquivOfTranscendental ℚ t ht).surjective s
  have : algebraMap (Algebra.adjoin ℚ {t}) K s = aeval t p := by
    rw [← hp]; exact coe_algEquivOfTranscendental t ht p
  rw [this, D₁.map_aeval, D₂.map_aeval, h]

private theorem eq_smul_derivAlong (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K]
    (D : Derivation ℚ K K) : D = D t • derivAlong t :=
  derivation_ext_of_eq ht _ _ (by simp [derivAlong_self ht])

theorem derivAlong_eq_smul (s : K) (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong s = derivAlong s t • derivAlong t :=
  eq_smul_derivAlong ht _

theorem derivAlong_mul_derivAlong {s : K} (hs : Transcendental ℚ s) [Algebra.IsAlgebraic ℚ⟮s⟯ K]
    (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t s * derivAlong s t = 1 := by
  have := congrArg (· s) (derivAlong_eq_smul s ht)
  simp only [derivAlong_self hs, Derivation.smul_apply, smul_eq_mul] at this
  rw [this, mul_comm]


end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv
