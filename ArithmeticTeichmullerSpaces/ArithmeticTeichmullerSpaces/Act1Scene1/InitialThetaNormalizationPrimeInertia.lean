import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineNormalizationPrimeInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionGroups

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Homs.lean`, inertia_fixes_Q.
fidelity: in a finite extension containing the same seed's full division field,
actual inertia at a nonzero normalization prime, relative to the base curve,
fixes the same seed's actual unsigned covering field.
boundary: Scene1/Derived. The ramification-index comparison, unramified covering,
the global cartesian square and the geometric producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] Genuine.primeNormalizationSeparable Genuine.primeNormalizationCoeffComm
  Genuine.normalizationFieldRingAction Genuine.primeNormalizationDedekind
  Genuine.primeNormalizationFraction
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)
variable (N : IntermediateField (Genuine.xLine S.prime.EK) S.functionFieldClosure)
  [FiniteDimensional (Genuine.xLine S.prime.EK) N]

theorem functionFieldCoverField_fixed_of_normalizationPrimeInertia
    (hN : Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false ≤ N)
    (hyN : Genuine.yG S.prime.EK ∈ N)
    (p : IsDedekindDomain.HeightOneSpectrum
      (FunctionFieldNormalization.coordRing (Genuine.xG S.prime.EK) N))
    (τ : N ≃ₐ[Genuine.xLine S.prime.EK] N)
    (hτ : τ ∈ p.asIdeal.inertia (N ≃ₐ[Genuine.xLine S.prime.EK] N))
    (hτy : τ ⟨Genuine.yG S.prime.EK, hyN⟩ = ⟨Genuine.yG S.prime.EK, hyN⟩)
    (a : N) (ha : (a : S.functionFieldClosure) ∈ S.functionFieldCoverField false) :
    τ a = a :=
  Genuine.normalizationPrime_inertia_fixes_unsignedField S.prime.EK N S.prime.ℓ hN hyN p τ
    hτ hτy S.prime.M a ha

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
