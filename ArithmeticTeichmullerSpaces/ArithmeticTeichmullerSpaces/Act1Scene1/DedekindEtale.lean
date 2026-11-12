/-
Compatibility proof adapted from Mathlib/RingTheory/RamificationInertia/Ramification.lean,
commit 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3.
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib `Ideal.ramificationIdx_eq_one_iff`,
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` and the etale locus.
fidelity: a finite injective inclusion of Dedekind domains over a characteristic
zero field is etale if its ramification index is one at every closed point.
boundary: Scene1/Derived. The arithmetic consumer proves the index hypothesis
for its actual normalization inclusion.
-/

namespace JoshiTeich.Act1Scene1.DedekindEtale

universe u v w
variable {K : Type u} [Field K] [CharZero K]
variable {R : Type v} {S : Type w} [CommRing R] [CommRing S]

theorem residueField_charZero [Algebra K R] (p : Ideal R) [p.IsPrime] :
    CharZero p.ResidueField := by
  let f : K →+* p.ResidueField := (algebraMap R p.ResidueField).comp (algebraMap K R)
  exact charZero_of_injective_ringHom f.injective

variable [Algebra R S]

/-- Compatibility proof of Mathlib 389347a's zero-prime ramification lemma.
The localization and quotient here are the original ones. -/
theorem ramificationIdx_bot_one [IsDomain S] :
    (⊥ : Ideal S).ramificationIdx R = 1 := by
  let Sq := Localization.AtPrime (⊥ : Ideal S)
  have hmap : Ideal.map (algebraMap R S)
      (Ideal.comap (algebraMap R S) (⊥ : Ideal S)) = ⊥ :=
    le_bot_iff.mp Ideal.map_comap_le
  rw [Ideal.ramificationIdx_def, IsScalarTower.algebraMap_eq R S Sq,
    ← Ideal.map_map, Ideal.under, hmap, Ideal.map_bot,
    ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]

theorem finitePresentation_of_finite [IsNoetherianRing R] [Module.Finite R S] :
    Algebra.FinitePresentation R S :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Closed points and the generic point together exhaust this prime spectrum. -/
theorem ramificationIdx_one_at_prime [IsDedekindDomain S]
    (h : ∀ (q : Ideal S), q.IsMaximal → q.ramificationIdx R = 1)
    (q : Ideal S) [q.IsPrime] : q.ramificationIdx R = 1 := by
  by_cases hq : q = ⊥
  · subst q
    exact ramificationIdx_bot_one
  · exact h q (Ideal.IsPrime.isMaximal inferInstance hq)

/-- Finiteness supplies finite presentation, and injectivity supplies flatness. -/
theorem etale_of_closed_ramificationIdx_one [Algebra K R]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    (h : ∀ (q : Ideal S), q.IsMaximal → q.ramificationIdx R = 1) :
    Algebra.Etale R S := by
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Module.Flat R S := inferInstance
  have : Algebra.FinitePresentation R S := finitePresentation_of_finite
  apply Algebra.etaleLocus_eq_univ_iff_etale.mp
  apply Set.eq_univ_iff_forall.mpr
  intro q
  have : CharZero (q.asIdeal.under R).ResidueField :=
    residueField_charZero (K := K) _
  have : PerfectField (q.asIdeal.under R).ResidueField := inferInstance
  have : Algebra.IsUnramifiedAt R q.asIdeal :=
    Ideal.ramificationIdx_eq_one_iff.mp (ramificationIdx_one_at_prime h q.asIdeal)
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q.asIdeal

end JoshiTeich.Act1Scene1.DedekindEtale
