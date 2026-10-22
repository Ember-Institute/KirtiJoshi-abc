import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedFieldAction

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's finite faithful action and fixed-field Galois comparison.
fidelity: the same seed's unsigned fixed field is finite Galois over its signed
fixed field. The existing quotient action is surjective onto all automorphisms,
and the degree equals the quotient order and divides two.
boundary: Scene1/Derived. Orbicurve realization, etale covering comparison and
ramification-stabilizer identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] signedCoverFieldAlgebra
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance signedCoverFieldModule :
    Module (S.functionFieldCoverField true) (S.functionFieldCoverField false) :=
  @Algebra.toModule _ _ _ _ S.signedCoverFieldAlgebra

theorem signedCoverField_isGalois :
    IsGalois (S.functionFieldCoverField true) (S.functionFieldCoverField false) :=
  Genuine.signedField_isGalois S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverField_finiteDimensional :
    FiniteDimensional (S.functionFieldCoverField true) (S.functionFieldCoverField false) :=
  Genuine.signedField_finiteDimensional S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverQuotientFieldAut_surjective :
    Function.Surjective S.signedCoverQuotientFieldAut :=
  Genuine.signedQuotientFieldAut_surjective S.prime.EK S.prime.ℓ S.prime.M

/-- The existing seed action gives the complete relative Galois group. -/
def signedCoverFieldGaloisEquiv : S.signedCoverQuotientGroup ≃*
    (S.functionFieldCoverField false ≃ₐ[S.functionFieldCoverField true]
      S.functionFieldCoverField false) :=
  Genuine.signedFieldGaloisEquiv S.prime.EK S.prime.ℓ S.prime.M

@[simp] theorem signedCoverFieldGaloisEquiv_apply (q : S.signedCoverQuotientGroup) :
    S.signedCoverFieldGaloisEquiv q = S.signedCoverQuotientFieldAut q := rfl

theorem signedCoverField_finrank_eq_card :
    Module.finrank (S.functionFieldCoverField true) (S.functionFieldCoverField false) =
      Nat.card S.signedCoverQuotientGroup :=
  Genuine.signedField_finrank_eq_card S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverField_finrank_dvd_two :
    Module.finrank (S.functionFieldCoverField true) (S.functionFieldCoverField false) ∣ 2 :=
  Genuine.signedField_finrank_dvd_two S.prime.EK S.prime.ℓ S.prime.M

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
