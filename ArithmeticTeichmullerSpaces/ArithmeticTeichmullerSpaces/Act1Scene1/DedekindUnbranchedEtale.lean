import ArithmeticTeichmullerSpaces.Act1Scene1.BranchEtaleRestriction

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); ramification in the actual normalization square;
Mathlib's ramification-one and flat etale criteria.
fidelity: a finite Dedekind inclusion is etale on a specified principal open
when its closed-point indices there are one. No index is prescribed outside
that open.
boundary: Scene1/Derived. The seed consumer proves the required indices from
the original two-torsion branch polynomial and the ramification tower law.
-/

namespace JoshiTeich.Act1Scene1.DedekindUnbranchedEtale

open scoped Classical
universe u
noncomputable section
variable {k R A : Type u} [Field k] [CharZero k] [CommRing R] [CommRing A]
variable [Algebra k R] [Algebra R A] [IsDedekindDomain R] [IsDedekindDomain A]
variable [Module.Finite R A]

include k

theorem isEtaleAt_of_index_one (hinj : Function.Injective (algebraMap R A))
    (q : Ideal A) [q.IsPrime] (hq : q.ramificationIdx R = 1) :
    Algebra.IsEtaleAt R q := by
  haveI : Module.IsTorsionFree R A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Flat R A := inferInstance
  haveI : Algebra.FinitePresentation R A := DedekindEtale.finitePresentation_of_finite
  haveI : CharZero (q.under R).ResidueField := DedekindEtale.residueField_charZero (K := k) _
  haveI : PerfectField (q.under R).ResidueField := inferInstance
  haveI : Algebra.IsUnramifiedAt R q := Ideal.ramificationIdx_eq_one_iff.mp hq
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q

theorem etale_away_of_closed_index_one (hinj : Function.Injective (algebraMap R A))
    (d : R) (h : ∀ q : Ideal A, q.IsMaximal → d ∉ q.under R → q.ramificationIdx R = 1) :
    Algebra.Etale R (Localization.Away (algebraMap R A d)) := by
  haveI : Algebra.FinitePresentation R A := DedekindEtale.finitePresentation_of_finite
  apply Algebra.basicOpen_subset_etaleLocus_iff_etale.mp
  intro q hd
  apply isEtaleAt_of_index_one (k := k) hinj
  by_cases hq : q.asIdeal = ⊥
  · rw [hq]
    exact DedekindEtale.ramificationIdx_bot_one
  · exact h q.asIdeal (Ideal.IsPrime.isMaximal inferInstance hq) hd

end
end JoshiTeich.Act1Scene1.DedekindUnbranchedEtale
