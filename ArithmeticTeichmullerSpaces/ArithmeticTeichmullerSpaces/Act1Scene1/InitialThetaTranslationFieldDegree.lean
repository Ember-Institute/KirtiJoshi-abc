import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineTorsionTranslationGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaTranslationIndex

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the actual seed torsion quotient and its proved fixed-field Galois action.
fidelity: consumes the field-action degree theorem with the seed's same TK,
M, and admissible prime. The original two Hgp fixed fields have degree ell.
No field-degree, group-index, or geometry law is supplied by the caller.
boundary: Scene1/Derived. This does not identify the normalization infinity
fiber or an AG cusp with the torsion quotient.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The two actual translation fixed fields have the seed's admissible degree. -/
theorem functionFieldCoverTranslation_finrank_eq_ell :
    letI := Genuine.torsionTranslationFieldAlgebra S.prime.EK S.prime.ℓ
      S.prime.TK S.prime.M S.prime.M_le_TK
    letI : Module
        (Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.TK false)
        (Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.M false) :=
      @Algebra.toModule _ _ _ _
        (Genuine.torsionTranslationFieldAlgebra S.prime.EK S.prime.ℓ
          S.prime.TK S.prime.M S.prime.M_le_TK)
    Module.finrank
      (Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.TK false)
      (Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.M false) = S.prime.ℓ := by
  letI := Genuine.torsionTranslationFieldAlgebra S.prime.EK S.prime.ℓ
    S.prime.TK S.prime.M S.prime.M_le_TK
  letI : Module
      (Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.TK false)
      (Genuine.stabilizerField S.prime.EK S.prime.ℓ S.prime.M false) :=
    @Algebra.toModule _ _ _ _
      (Genuine.torsionTranslationFieldAlgebra S.prime.EK S.prime.ℓ
        S.prime.TK S.prime.M S.prime.M_le_TK)
  exact (Genuine.torsionTranslationField_finrank_eq_card_torsionQuotient
    S.prime.EK S.prime.ℓ S.prime.ℓ_prime.pos S.prime.TK le_rfl
      S.prime.M S.prime.M_le_TK).trans S.prime.card_rankOneQuotient

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
