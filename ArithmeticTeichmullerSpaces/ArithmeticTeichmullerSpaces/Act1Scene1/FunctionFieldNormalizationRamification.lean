/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/SubfieldRamified.lean`
original-author: Christian Merten <lana@merten.dev> (Git author; no author header in source)
original-commit: `a4f556329cb56910f3d258ee81552c85b0d94b56`
positivity-source: `refer/iut/Iut/Anabelian/Genuine/Realize.lean`, `pmMult_pos`
positivity-original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
positivity-original-notice:
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f` (pi1 package)
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package LICENSE; the source has no per-file copyright
notice and the package has no NOTICE file. The project retains the license text.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`SubfieldRamified.lean`, `finite_ramified`.
fidelity: ports the proof that nontrivial ramification indices occur at finitely
many maximal ideals, using the nonzero different and its prime factors. Defines
the index by Mathlib's chosen prime above the base ideal and proves positivity.
boundary: Scene1/Derived; no Galois symmetry or stabilizer-order identification
is assumed for an arbitrary field inclusion.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationFinite
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.RamificationInertia.Galois

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin Classical
universe u
noncomputable section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k]
variable {t : Ω} {F N : IntermediateField (rationalBase k t) Ω}

/-- The actual ramification index at Mathlib's chosen prime above the base ideal. -/
def ramificationMultiplicity (hFN : F ≤ N) (v : Ideal (coordRing t F)) : ℕ :=
  letI := ringMapAlgebra hFN
  v.ramificationIdxIn (coordRing t N)

noncomputable abbrev ringMapFieldAlgebra (hFN : F ≤ N) : Algebra (coordRing t F) N :=
  ((algebraMap (coordRing t N) N).comp (ringMap hFN).toRingHom).toAlgebra

lemma ramificationMultiplicity_pos [FiniteDimensional (rationalBase k t) N]
    [Algebra.IsSeparable (rationalBase k t) N]
    (ht : Transcendental k t) (hFN : F ≤ N)
    (v : Ideal (coordRing t F)) (hv : v.IsMaximal) :
    0 < ramificationMultiplicity hFN v := by
  letI iR := ringMapAlgebra hFN
  letI : SMul (coordRing t F) (coordRing t N) := iR.toSMul
  letI : Module (coordRing t F) (coordRing t N) := iR.toModule
  haveI := moduleFinite_ringMap ht hFN
  haveI := dedekindRing t ht N
  haveI : Algebra.IsIntegral (coordRing t F) (coordRing t N) := ⟨ringMap_isIntegral hFN⟩
  haveI : FaithfulSMul (coordRing t F) (coordRing t N) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact ringMap_injective hFN
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := coordRing t N) v
  have hex : ∃ P : Ideal (coordRing t N), P.IsPrime ∧ P.LiesOver v :=
    ⟨P, hP.isPrime, hPl⟩
  unfold ramificationMultiplicity
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  have := hex.choose_spec.1
  exact Ideal.ramificationIdx_pos _ _

variable [FiniteDimensional (rationalBase k t) N]
variable (ht : Transcendental k t) (hFN : F ≤ N)
include ht

/-- Nontrivial ramification multiplicities have finite support on the closed points. -/
theorem finite_ramificationMultiplicity :
    {v : Ideal (coordRing t F) | v.IsMaximal ∧
      ramificationMultiplicity hFN v ≠ 1}.Finite := by
  classical
  letI iR := ringMapAlgebra hFN
  letI : SMul (coordRing t F) (coordRing t N) := iR.toSMul
  letI : Module (coordRing t F) (coordRing t N) := iR.toModule
  letI : Algebra F N := (IntermediateField.inclusion hFN).toAlgebra
  letI : Algebra (coordRing t F) N := ringMapFieldAlgebra hFN
  haveI : FiniteDimensional (rationalBase k t) F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFN).toLinearMap
      (IntermediateField.inclusion hFN).injective
  haveI : CharZero (rationalBase k t) := charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI : Algebra.IsSeparable (rationalBase k t) N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable (rationalBase k t) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsScalarTower (rationalBase k t) F N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional F N := FiniteDimensional.right (rationalBase k t) F N
  haveI : Algebra.IsSeparable F N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI := fractionFieldRing t F
  haveI := fractionFieldRing t N
  haveI := dedekindRing t ht F
  haveI := dedekindRing t ht N
  haveI := moduleFinite_ringMap ht hFN
  haveI : Module.IsTorsionFree (coordRing t F) (coordRing t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective hFN
  haveI : FaithfulSMul (coordRing t F) (coordRing t N) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact ringMap_injective hFN
  haveI : Algebra.IsIntegral (coordRing t F) (coordRing t N) := ⟨ringMap_isIntegral hFN⟩
  letI : Algebra (coordRing t F) F := (coordRing t F).toAlgebra
  letI : Algebra (coordRing t N) N := (coordRing t N).toAlgebra
  letI : IsScalarTower (coordRing t F) F N := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  letI : IsScalarTower (coordRing t F) (coordRing t N) N := ⟨fun a b c => by
    change (((IntermediateField.inclusion hFN (a : F) : N) * (b : N)) * c) =
      (IntermediateField.inclusion hFN (a : F) : N) * ((b : N) * c)
    rw [← mul_assoc]⟩
  set D := differentIdeal (coordRing t F) (coordRing t N)
  haveI : Algebra.IsSeparable (FractionRing (coordRing t F))
      (FractionRing (coordRing t N)) := by
    haveI : CharZero (FractionRing (coordRing t F)) := inferInstance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hD : D ≠ ⊥ := differentIdeal_ne_bot
  let T : Finset (Ideal (coordRing t N)) :=
    (UniqueFactorizationMonoid.normalizedFactors D).toFinset
  refine ((T.finite_toSet.image
    (fun P => P.comap (algebraMap (coordRing t F) (coordRing t N)))).union
    (Set.finite_singleton (⊥ : Ideal (coordRing t F)))).subset ?_
  have prime_over : ∀ (v : Ideal (coordRing t F)), v.IsMaximal →
      v.ramificationIdxIn (coordRing t N) ≠ 1 →
      ∃ P : Ideal (coordRing t N), P.IsPrime ∧ P ∣ D ∧
        P.comap (algebraMap (coordRing t F) (coordRing t N)) = v := by
    intro v hv hne
    have hex : ∃ P : Ideal (coordRing t N), P.IsPrime ∧ P.LiesOver v := by
      obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := coordRing t N) v
      exact ⟨P, hP.isPrime, hPl⟩
    have hdef : v.ramificationIdxIn (coordRing t N) =
        hex.choose.ramificationIdx (coordRing t F) := by
      rw [Ideal.ramificationIdxIn, dif_pos hex]
    obtain ⟨hP, hPl⟩ := hex.choose_spec
    set P := hex.choose
    have hP1 : P ∣ D := by
      rw [dvd_differentIdeal_iff]
      intro hunr
      have heq : P.ramificationIdx (coordRing t F) = 1 :=
        Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      exact hne (hdef.trans heq)
    exact ⟨P, hP, hP1, hPl.over.symm⟩
  rintro v ⟨hv, hne⟩
  change v.ramificationIdxIn (coordRing t N) ≠ 1 at hne
  by_cases hvb : v = ⊥
  · exact Or.inr hvb
  left
  obtain ⟨P, hP, hP1, hPv⟩ := prime_over v hv hne
  refine ⟨P, ?_, hPv⟩
  simp only [T, Multiset.mem_toFinset, Finset.mem_coe]
  have hPbot : P ≠ ⊥ := by
    intro h
    have hv0 : v = ⊥ := by simpa [h] using hPv.symm
    apply hne
    rw [hv0, Ideal.ramificationIdxIn]
    split <;> simp_all
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hD).mpr
    ⟨(Ideal.prime_of_isPrime hPbot hP).irreducible, normalize_eq P, hP1⟩

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
