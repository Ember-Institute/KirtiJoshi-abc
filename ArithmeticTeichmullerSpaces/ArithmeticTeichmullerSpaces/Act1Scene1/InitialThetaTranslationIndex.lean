import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineTorsionTranslationQuotient
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaTorsionQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the seed's actual global torsion quotient and the proved ambient translations.
fidelity: specializes the actual Hgp quotient and index to the seed's own
EK, admissible prime, full torsion TK and rank-one line M. The quotient is
the already constructed rankOneQuotient, whose order is the same ell.
No new subgroup, cardinality, or source law is supplied by the caller.
boundary: Scene1/Derived. This does not identify infinity fibers with the
torsion quotient, construct an AG.Cusp, or prove the geometry producer.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The seed's actual smaller Hgp subgroup is normal in its full torsion translation subgroup. -/
theorem functionFieldCoverGroup_translation_normal :
    ((Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.M false).subgroupOf
      (Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.TK false)).Normal :=
  Genuine.torsionTranslationKernel_normal S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.TK le_rfl S.prime.M S.prime.M_le_TK

/-- The actual translation quotient is the seed's previously constructed rank-one quotient. -/
def functionFieldCoverTranslationQuotientEquiv :
    letI := S.functionFieldCoverGroup_translation_normal
    Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.TK false ⧸
      (Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.M false).subgroupOf
        (Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.TK false) ≃*
      Multiplicative S.prime.rankOneQuotient :=
  Genuine.torsionTranslationQuotientEquiv S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.TK le_rfl S.prime.M S.prime.M_le_TK

/-- The seed's actual covering subgroup has precisely ell cosets in its full torsion subgroup. -/
theorem functionFieldCoverGroup_relIndex_eq_ell :
    (Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.M false).relIndex
      (Genuine.Hgp S.prime.EK S.prime.ℓ S.prime.TK false) = S.prime.ℓ :=
  (Genuine.Hgp_relIndex_eq_card_torsionQuotient S.prime.EK S.prime.ℓ
    S.prime.ℓ_prime.pos S.prime.TK le_rfl S.prime.M S.prime.M_le_TK).trans
      S.prime.card_rankOneQuotient

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
