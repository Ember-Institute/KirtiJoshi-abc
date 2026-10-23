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

theorem finitePresentation_of_finite [IsNoetherianRing R] [Module.Finite R S] :
    Algebra.FinitePresentation R S :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Closed points and the generic point together exhaust this prime spectrum. -/
theorem ramificationIdx_one_at_prime [IsDedekindDomain S]
    (h : ∀ (q : Ideal S), q.IsMaximal → q.ramificationIdx R = 1)
    (q : Ideal S) [q.IsPrime] : q.ramificationIdx R = 1 := by
  by_cases hq : q = ⊥
  · subst q
    exact Ideal.ramificationIdx_bot_eq_one R
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
  have : Algebra.HasSeparableResidueFieldsAt R S (q.asIdeal.under R) := inferInstance
  have : Algebra.IsUnramifiedAt R q.asIdeal :=
    Ideal.ramificationIdx_eq_one_iff.mp (ramificationIdx_one_at_prime h q.asIdeal)
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q.asIdeal

end JoshiTeich.Act1Scene1.DedekindEtale
