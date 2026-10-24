import ArithmeticTeichmullerSpaces.Act1Scene1.DedekindEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Restrict

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); the ramification-one criterion over a
characteristic-zero field and the actual two-torsion branch polynomial.
fidelity: a closed-point branch formula determines the entire etale locus
of a finite Dedekind inclusion. Its original Spec map is etale after
restriction to the complement of the specified base branch element.
boundary: Scene1/Derived. The arithmetic consumer supplies the branch formula.
-/

namespace JoshiTeich.Act1Scene1.BranchEtaleRestriction

open CategoryTheory AlgebraicGeometry
open scoped Classical
universe u
noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

theorem awayMap_etale (r : R)
    [Algebra.Etale R (Localization.Away (algebraMap R A r))] :
    (Localization.awayMap (algebraMap R A) r).Etale := by
  let φ : Localization.Away r →ₐ[R] Localization.Away (algebraMap R A r) :=
    Localization.awayMapₐ (Algebra.ofId R A) r
  letI : Algebra (Localization.Away r) (Localization.Away (algebraMap R A r)) :=
    φ.toRingHom.toAlgebra
  letI : IsScalarTower R (Localization.Away r) (Localization.Away (algebraMap R A r)) :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.Etale (Localization.Away r) (Localization.Away (algebraMap R A r)) :=
    Algebra.Etale.of_restrictScalars R (Localization.Away r)
      (Localization.Away (algebraMap R A r))
  exact RingHom.etale_algebraMap.mpr inferInstance

theorem spec_restrict_etale (r : R)
    [Algebra.Etale R (Localization.Away (algebraMap R A r))] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap R A)) ∣_ PrimeSpectrum.basicOpen r) := by
  letI : MorphismProperty.RespectsIso (@Etale.{u}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro X Y Z e f hf
      haveI := hf
      infer_instance
    · intro X Y Z e f hf
      haveI := hf
      infer_instance
  exact (MorphismProperty.arrow_mk_iso_iff (@Etale.{u})
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R A)) r)).mpr
      (HasRingHomProperty.Spec_iff.mpr (awayMap_etale r))

variable {k : Type u} [Field k] [CharZero k] [Algebra k R]
variable [IsDedekindDomain R] [IsDedekindDomain A] [Module.Finite R A]
variable (hinj : Function.Injective (algebraMap R A)) (d : R) (hd : d ≠ 0)
variable (hbranch : ∀ q : Ideal A, q.IsMaximal →
  q.ramificationIdx R = if d ∈ q.under R then 2 else 1)

include k hinj hd hbranch

theorem isEtaleAt_iff (q : Ideal A) [q.IsPrime] :
    Algebra.IsEtaleAt R q ↔ d ∉ q.under R := by
  haveI : Module.IsTorsionFree R A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Flat R A := inferInstance
  haveI : Algebra.FinitePresentation R A := DedekindEtale.finitePresentation_of_finite
  haveI : CharZero (q.under R).ResidueField := DedekindEtale.residueField_charZero (K := k) _
  haveI : Algebra.HasSeparableResidueFieldsAt R A (q.under R) := inferInstance
  have hi : q.ramificationIdx R = 1 ↔ Algebra.IsEtaleAt R q := by
    rw [Ideal.ramificationIdx_eq_one_iff]
    constructor
    · intro h
      haveI := h
      exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q
    · intro h
      haveI := h
      infer_instance
  apply hi.symm.trans
  by_cases hq : q = ⊥
  · subst q
    constructor
    · intro _ h
      change algebraMap R A d = 0 at h
      exact hd (hinj (h.trans (map_zero _).symm))
    · intro _
      exact Ideal.ramificationIdx_bot_eq_one R
  · rw [hbranch q (Ideal.IsPrime.isMaximal inferInstance hq)]
    by_cases h : d ∈ q.under R <;> simp [h]

theorem etaleLocus_eq_basicOpen :
    Algebra.etaleLocus R A = PrimeSpectrum.basicOpen (algebraMap R A d) := by
  ext q
  exact isEtaleAt_iff (k := k) hinj d hd hbranch q.asIdeal

theorem etale_away_branch : Algebra.Etale R (Localization.Away (algebraMap R A d)) := by
  haveI : Algebra.FinitePresentation R A := DedekindEtale.finitePresentation_of_finite
  apply Algebra.basicOpen_subset_etaleLocus_iff_etale.mp
  rw [etaleLocus_eq_basicOpen (k := k) hinj d hd hbranch]

end
end JoshiTeich.Act1Scene1.BranchEtaleRestriction
