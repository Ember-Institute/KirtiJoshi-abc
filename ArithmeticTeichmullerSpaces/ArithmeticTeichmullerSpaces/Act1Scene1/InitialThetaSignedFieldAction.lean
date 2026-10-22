import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedFieldAction
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`Pi1/Orbifold/GaloisData.lean`, fixed-field action of a normalizing group.
fidelity: restricts the same seed's ambient signed group to its unsigned
function field, computes the kernel and constructs a faithful quotient action
over its signed function field. Evaluation agrees with the ambient action.
boundary: Scene1/Derived. This does not identify normalization-cover
or orbicurve automorphisms, stabilizer orders, or ramification multiplicities.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The base algebra comes from this seed's proved fixed-field inclusion. -/
@[instance_reducible] def signedCoverFieldAlgebra :
    Algebra (S.functionFieldCoverField true) (S.functionFieldCoverField false) :=
  Genuine.signedFieldAlgebra S.prime.EK S.prime.ℓ S.prime.M

attribute [local instance] signedCoverFieldAlgebra

/-- The signed cover group acts on the actual unsigned field over the signed field. -/
def signedCoverFieldAut : S.functionFieldCoverGroup true →*
    (S.functionFieldCoverField false ≃ₐ[S.functionFieldCoverField true]
      S.functionFieldCoverField false) :=
  Genuine.signedFieldAut S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverFieldAut_ker :
    S.signedCoverFieldAut.ker = S.functionFieldUnsignedSubgroup true :=
  Genuine.signedFieldAut_ker S.prime.EK S.prime.ℓ S.prime.M

/-- The actual signed quotient acts faithfully on the unsigned function field. -/
def signedCoverQuotientFieldAut : S.signedCoverQuotientGroup →*
    (S.functionFieldCoverField false ≃ₐ[S.functionFieldCoverField true]
      S.functionFieldCoverField false) :=
  Genuine.signedQuotientFieldAut S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverQuotientFieldAut_injective :
    Function.Injective S.signedCoverQuotientFieldAut :=
  Genuine.signedQuotientFieldAut_injective S.prime.EK S.prime.ℓ S.prime.M

/-- Quotient action evaluation is the original ambient Galois evaluation. -/
@[simp] theorem coe_signedCoverQuotientFieldAut (g : S.functionFieldCoverGroup true)
    (x : S.functionFieldCoverField false) :
    ((S.signedCoverQuotientFieldAut (S.signedCoverQuotientMap g) x :
      S.functionFieldCoverField false) : Genuine.Ω S.prime.EK) = g.val x.val := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
