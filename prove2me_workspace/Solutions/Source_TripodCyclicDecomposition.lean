/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CyclicLocal.lean (the decomposition group)
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlacesOver
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain
open scoped Pointwise

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

noncomputable local instance : MulSemiringAction (L ≃ₐ[F] L) (𝓞 L) :=
  IsIntegralClosure.MulSemiringAction (𝓞 F) F L (𝓞 L)

/-- An automorphism in the stabilizer of the prime defining a finite place fixes the place. -/
theorem galPlace_eq_of_mem_stabilizer (σ : L ≃ₐ[F] L) (w : FinitePlace L)
    (hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[F] L) w.maximalIdeal.asIdeal) :
    JoshiTeich.ReferenceIut.galPlace σ w = w := by
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_def] at hσ
  apply (FinitePlace.maximalIdeal_inj _ _).mp
  apply HeightOneSpectrum.ext
  rw [JoshiTeich.ReferenceIut.galPlace_maximalIdeal]
  have hinv : JoshiTeich.ReferenceIut.galRestrictInt σ⁻¹ =
      (JoshiTeich.ReferenceIut.galRestrictInt σ).symm := by
    rw [JoshiTeich.ReferenceIut.galRestrictInt, JoshiTeich.ReferenceIut.galRestrictInt,
      map_inv, AlgEquiv.aut_inv]
  rw [hinv]
  change w.maximalIdeal.asIdeal.comap
    (JoshiTeich.ReferenceIut.galRestrictInt σ).toRingEquiv.symm = w.maximalIdeal.asIdeal
  rw [Ideal.comap_symm]
  exact hσ

variable [IsGalois F L]

local instance : IsGaloisGroup (L ≃ₐ[F] L) (𝓞 F) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing (L ≃ₐ[F] L) (𝓞 F) (𝓞 L) F L

/-- The relative ramification index divides the size of the decomposition group. -/
theorem ramificationIdx'_dvd_card_stabilizer {w : FinitePlace L} {v : FinitePlace F}
    (hwv : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal) :
    v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal ∣
      Nat.card (MulAction.stabilizer (L ≃ₐ[F] L) w.maximalIdeal.asIdeal) := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsPrime := v.maximalIdeal.isPrime
  haveI : w.maximalIdeal.asIdeal.IsPrime := w.maximalIdeal.isPrime
  haveI : Finite (𝓞 F ⧸ v.maximalIdeal.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ v.maximalIdeal.ne_bot
  rw [Ideal.card_stabilizer_eq (G := L ≃ₐ[F] L) v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      (L ≃ₐ[F] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal
      v.maximalIdeal.ne_bot]
  exact dvd_mul_right _ _

/-- A prime divisor of the relative ramification index gives an automorphism of that
order which fixes the place. -/
theorem exists_orderOf_eq_of_dvd_ramificationIdx {w : FinitePlace L} {v : FinitePlace F}
    (hwv : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hram : ℓ ∣ v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal) :
    ∃ σ : L ≃ₐ[F] L, JoshiTeich.ReferenceIut.galPlace σ w = w ∧ orderOf σ = ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨⟨σ, hσ⟩, hord⟩ :=
    exists_prime_orderOf_dvd_card' ℓ (hram.trans (ramificationIdx'_dvd_card_stabilizer hwv))
  rw [← Subgroup.orderOf_coe] at hord
  exact ⟨σ, galPlace_eq_of_mem_stabilizer σ w hσ, hord⟩

end AbcAdaptation.Reference.Iut
