import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaNormalizationFinite
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationRamification

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Realize.lean`, ramification multiplicities.
fidelity: assigns to the same seed's signed normalization the actual ramification
indices of its unsigned cover; assigns multiplicity one to the unsigned curve.
Proves positivity on closed points and finite support of nontrivial multiplicity.
boundary: Scene1/Derived. Equality with group stabilizer orders, orbicurve etale
covering, cartesianness, core and theta-root identification remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped IntermediateField.algebraAdjoinAdjoin Classical
universe u
noncomputable section

set_option synthInstance.maxHeartbeats 1000000
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- Ramification multiplicity of the actual signed normalization extension. -/
def signedCoverRamificationMultiplicity (v : Ideal (S.coverNormalizationRing true)) : ℕ :=
  FunctionFieldNormalization.ramificationMultiplicity
    (Genuine.normalizationField_signed_le_unsigned S.prime.EK S.prime.ℓ S.prime.M) v

theorem signedCoverRamificationMultiplicity_pos
    (v : Ideal (S.coverNormalizationRing true)) (hv : v.IsMaximal) :
    0 < S.signedCoverRamificationMultiplicity v :=
  FunctionFieldNormalization.ramificationMultiplicity_pos
    (Genuine.transcendental_xG S.prime.EK) _ v hv

theorem signedCoverRamificationMultiplicity_finite :
    {v : Ideal (S.coverNormalizationRing true) |
      v.IsMaximal ∧ S.signedCoverRamificationMultiplicity v ≠ 1}.Finite :=
  FunctionFieldNormalization.finite_ramificationMultiplicity
    (Genuine.transcendental_xG S.prime.EK) _

/-- Unsigned multiplicities are one; signed multiplicities come from the actual cover. -/
def coverNormalizationMultiplicity : (pm : Bool) → Ideal (S.coverNormalizationRing pm) → ℕ
  | false => fun _ => 1
  | true => S.signedCoverRamificationMultiplicity

theorem coverNormalizationMultiplicity_pos (pm : Bool)
    (v : Ideal (S.coverNormalizationRing pm)) (hv : v.IsMaximal) :
    0 < S.coverNormalizationMultiplicity pm v := by
  cases pm
  · exact Nat.one_pos
  · exact S.signedCoverRamificationMultiplicity_pos v hv

theorem coverNormalizationMultiplicity_finite (pm : Bool) :
    {v : Ideal (S.coverNormalizationRing pm) |
      v.IsMaximal ∧ S.coverNormalizationMultiplicity pm v ≠ 1}.Finite := by
  cases pm
  · simp [coverNormalizationMultiplicity]
  · exact S.signedCoverRamificationMultiplicity_finite

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
