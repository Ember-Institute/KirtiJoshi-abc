import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedNormalizationAction
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalization
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`Pi1/Orbifold/GaloisData.lean`, actual normalization-ring action.
fidelity: the same seed's signed quotient acts faithfully on its unsigned
normalization ring, agrees with ambient evaluation, and fixes the signed image.
boundary: Scene1/Derived. The orbicurve producer, etale covering comparison,
full automorphism identification and ramification-stabilizer identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The actual quotient acts by ring automorphisms on the unsigned normalization. -/
def signedCoverQuotientNormalizationAut :
    S.signedCoverQuotientGroup →* RingAut (S.coverNormalizationRing false) :=
  Genuine.signedQuotientNormalizationAut S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverQuotientNormalizationAut_injective :
    Function.Injective S.signedCoverQuotientNormalizationAut :=
  Genuine.signedQuotientNormalizationAut_injective S.prime.EK S.prime.ℓ S.prime.M

/-- Normalization evaluation is the original ambient Galois evaluation. -/
@[simp] theorem coe_signedCoverQuotientNormalizationAut
    (g : S.functionFieldCoverGroup true) (x : S.coverNormalizationRing false) :
    (((S.signedCoverQuotientNormalizationAut (S.signedCoverQuotientMap g) x :
      S.coverNormalizationRing false) :
      Genuine.normalizationField S.prime.EK S.prime.ℓ S.prime.M false) :
        Genuine.Ω S.prime.EK) = g.val x.val.val := rfl

theorem signedCoverQuotientNormalizationAut_fixed_signed
    (q : S.signedCoverQuotientGroup) (a : S.coverNormalizationRing true) :
    S.signedCoverQuotientNormalizationAut q (S.signedCoverNormalizationRingMap a) =
      S.signedCoverNormalizationRingMap a :=
  Genuine.signedQuotientNormalizationAut_fixed_signed S.prime.EK S.prime.ℓ S.prime.M q a

theorem signedCoverNormalizationInvariant_iff
    (x : S.coverNormalizationRing false) :
    Genuine.signedNormalizationInvariant S.prime.EK S.prime.ℓ S.prime.M x ↔
      ∃ a : S.coverNormalizationRing true,
        S.signedCoverNormalizationRingMap a = x :=
  Genuine.signedNormalizationInvariant_iff S.prime.EK S.prime.ℓ S.prime.M x

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
