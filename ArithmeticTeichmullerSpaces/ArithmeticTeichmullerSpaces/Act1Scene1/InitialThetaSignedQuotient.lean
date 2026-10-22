import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedQuotient
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionGroups
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Orbifold.lean`, `conj_mem_Hgp_false`.
fidelity: constructs the finite signed/unsigned group quotient for the same
arithmetic seed, proves that its order divides two, and identifies its
quotient-map kernel with the actual unsigned torsion-translation condition.
Finiteness follows from the proved
openness of that subgroup in the compact function-field Galois group.
boundary: Scene1/Derived. The quotient is not yet identified with the
automorphisms of the normalization cover or with its ramification stabilizers.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The actual unsigned subgroup, regarded inside the chosen cover group. -/
abbrev functionFieldUnsignedSubgroup (pm : Bool) : Subgroup (S.functionFieldCoverGroup pm) :=
  (S.functionFieldCoverGroup false).subgroupOf (S.functionFieldCoverGroup pm)

instance functionFieldUnsignedSubgroup_normal (pm : Bool) :
    (S.functionFieldUnsignedSubgroup pm).Normal :=
  Genuine.Hgp_false_normal S.prime.EK S.prime.ℓ S.prime.M pm

/-- The actual signed cover group modulo its unsigned translation subgroup. -/
abbrev signedCoverQuotientGroup :=
  S.functionFieldCoverGroup true ⧸ S.functionFieldUnsignedSubgroup true

instance finite_signedCoverQuotientGroup : Finite S.signedCoverQuotientGroup :=
  Subgroup.quotient_finite_of_isOpen' (S.functionFieldCoverGroup true)
    (S.functionFieldUnsignedSubgroup true) (S.functionFieldCoverGroup_isOpen true)
    (Subgroup.subgroupOf_isOpen _ _ (S.functionFieldCoverGroup_isOpen false))

/-- The quotient homomorphism of the seed's actual signed cover group. -/
def signedCoverQuotientMap : S.functionFieldCoverGroup true →* S.signedCoverQuotientGroup :=
  QuotientGroup.mk' (S.functionFieldUnsignedSubgroup true)

theorem signedCoverQuotientMap_surjective : Function.Surjective S.signedCoverQuotientMap :=
  QuotientGroup.mk'_surjective _

theorem signedCoverQuotientMap_ker :
    S.signedCoverQuotientMap.ker = S.functionFieldUnsignedSubgroup true :=
  QuotientGroup.ker_mk' _

/-- Trivial quotient classes are precisely the actual torsion translations. -/
theorem signedCoverQuotientMap_eq_one_iff (σ : S.functionFieldCoverGroup true) :
    S.signedCoverQuotientMap σ = 1 ↔
      Genuine.act S.prime.EK σ.val (Genuine.Qpt S.prime.EK S.prime.ℓ) -
        Genuine.Qpt S.prime.EK S.prime.ℓ ∈
          Genuine.Mbar S.prime.EK S.prime.ℓ S.prime.M := by
  rw [← MonoidHom.mem_ker, S.signedCoverQuotientMap_ker]
  exact Genuine.mem_Hgp_false S.prime.EK

theorem signedCoverQuotientGroup_card_dvd_two : Nat.card S.signedCoverQuotientGroup ∣ 2 :=
  Genuine.Hgp_false_relIndex_dvd_two S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverQuotientGroup_card_le_two : Nat.card S.signedCoverQuotientGroup ≤ 2 :=
  Nat.le_of_dvd (by decide) S.signedCoverQuotientGroup_card_dvd_two

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
