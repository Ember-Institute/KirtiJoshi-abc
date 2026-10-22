import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedNormalizationGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedNormalizationAction
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationMultiplicity

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's Galois ramification and inertia cardinality comparisons.
fidelity: proves the Galois-group structure for the same seed's actual
normalization-ring inclusion. Its existing ramification multiplicity is the
inertia-group order at every prime above the base prime. Arithmetic prime
stabilizer orders retain the residue-degree factor.
boundary: Scene1/Derived. Geometric point comparison, orbicurve realization,
etaleness, cartesianness, core and theta-root identification remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical Pointwise
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

@[instance_reducible] def signedCoverNormalizationAlgebra :
    Algebra (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
  Genuine.signedNormalizationAlgebra S.prime.EK S.prime.ℓ S.prime.M

attribute [local instance] signedCoverNormalizationAlgebra

@[instance_reducible] def signedCoverNormalizationGaloisAction :
    MulSemiringAction S.signedCoverQuotientGroup (S.coverNormalizationRing false) :=
  Genuine.signedNormalizationGaloisAction S.prime.EK S.prime.ℓ S.prime.M

attribute [local instance] signedCoverNormalizationGaloisAction

local instance coverNormIdealAction :
    MulAction S.signedCoverQuotientGroup (Ideal (S.coverNormalizationRing false)) :=
  (Ideal.pointwiseDistribMulAction (M := S.signedCoverQuotientGroup)
    (R := S.coverNormalizationRing false)).toMulAction

@[simp] theorem signedCoverNormalization_smul (q : S.signedCoverQuotientGroup)
    (x : S.coverNormalizationRing false) :
    @SMul.smul S.signedCoverQuotientGroup (S.coverNormalizationRing false)
      S.signedCoverNormalizationGaloisAction.toDistribMulAction.toMulAction.toSMul q x =
        S.signedCoverQuotientNormalizationAut q x := rfl

theorem signedCoverNormalizationGaloisGroup :
    IsGaloisGroup S.signedCoverQuotientGroup
      (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
  Genuine.signedNormalizationGaloisGroup S.prime.EK S.prime.ℓ S.prime.M

theorem signedCoverRamificationMultiplicity_eq_ramificationIdx
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    S.signedCoverRamificationMultiplicity p = P.ramificationIdx (S.coverNormalizationRing true) :=
  Genuine.signedNormalizationMultiplicity_eq_ramificationIdx S.prime.EK S.prime.ℓ S.prime.M p P

theorem signedCoverRamificationMultiplicity_eq_card_inertia
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    S.signedCoverRamificationMultiplicity p = Nat.card (P.inertia S.signedCoverQuotientGroup) :=
  (Genuine.signedNormalization_card_inertia S.prime.EK S.prime.ℓ S.prime.M p P).symm

theorem signedCoverNormalization_card_stabilizer
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer S.signedCoverQuotientGroup P) =
      S.signedCoverRamificationMultiplicity p * p.inertiaDegIn (S.coverNormalizationRing false) :=
  Genuine.signedNormalization_card_stabilizer S.prime.EK S.prime.ℓ S.prime.M p P

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
