import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionPointInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionGroups

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Inertia.lean` and `Genuine/Cover.lean`.
fidelity: base-curve valuation inertia fixes the same seed's actual division
points and unsigned cover field. The subgroup conclusion uses its actual
admissible prime and chosen rank-one torsion line.
boundary: Scene1/Derived. Normalization-prime inertia comparison, unramified
covering, cartesianness, core and the full geometric producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem functionFieldDivisionPoint_fixed_of_valuationInertia
    (σ : Genuine.Gal S.prime.EK) (W : ValuationSubring S.functionFieldClosure)
    (hk : ∀ c : ↥S.prime.torsionField, algebraMap _ _ c ∈ W)
    (hx : Genuine.xG S.prime.EK ∈ W) (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (hG : Genuine.act S.prime.EK σ S.functionFieldGenericPoint = S.functionFieldGenericPoint)
    (n : ℕ) (hn : 0 < n) :
    Genuine.act S.prime.EK σ (S.functionFieldDivisionPoint n) = S.functionFieldDivisionPoint n :=
  Genuine.valuationInertia_fixes_divSys S.prime.EK σ W hk hx hσ hG n hn

theorem functionFieldCoverGroup_mem_of_valuationInertia
    (σ : Genuine.Gal S.prime.EK) (W : ValuationSubring S.functionFieldClosure)
    (hk : ∀ c : ↥S.prime.torsionField, algebraMap _ _ c ∈ W)
    (hx : Genuine.xG S.prime.EK ∈ W) (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (hG : Genuine.act S.prime.EK σ S.functionFieldGenericPoint = S.functionFieldGenericPoint) :
    σ ∈ S.functionFieldCoverGroup false :=
  Genuine.valuationInertia_mem_unsignedGroup S.prime.EK σ W hk hx hσ hG S.prime.ℓ S.prime.M

theorem functionFieldCoverField_fixed_of_valuationInertia
    (σ : Genuine.Gal S.prime.EK) (W : ValuationSubring S.functionFieldClosure)
    (hk : ∀ c : ↥S.prime.torsionField, algebraMap _ _ c ∈ W)
    (hx : Genuine.xG S.prime.EK ∈ W) (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (hG : Genuine.act S.prime.EK σ S.functionFieldGenericPoint = S.functionFieldGenericPoint)
    (x : S.functionFieldCoverField false) : σ (x : S.functionFieldClosure) = x :=
  Genuine.valuationInertia_fixes_unsignedField S.prime.EK σ W hk hx hσ hG S.prime.ℓ S.prime.M x

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
