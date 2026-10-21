import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.GenericPoint
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaTorsionQuotient

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Basic.lean` and `Orbifold.lean`.
fidelity: the genuine generic-point construction is evaluated on the same
arithmetic seed's curve over its torsion field. Global torsion embeds in this
ambient curve, and the function-field Galois action fixes its image.
boundary: Scene1/Derived. The function-field closure is distinct in purpose
from the seed's number-field closure. Covering/core/theta-root realization is open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The actual geometric ambient field of the seed's curve over its torsion field. -/
abbrev functionFieldClosure : Type u := Genuine.Ω S.prime.EK

/-- The same curve's generic point in its function-field algebraic closure. -/
def functionFieldGenericPoint :
    (S.prime.EK⁄S.functionFieldClosure).toAffine.Point :=
  Genuine.genericPoint S.prime.EK

/-- The actual geometric `x`-coordinate is transcendental over the torsion field. -/
theorem functionFieldGeneric_x_transcendental :
    Transcendental ↥S.prime.torsionField (Genuine.xG S.prime.EK) :=
  Genuine.transcendental_xG S.prime.EK

/-- Global torsion from the seed embeds in this same geometric ambient curve. -/
def functionFieldTorsionMap :
    ↥S.prime.TK →+ (S.prime.EK⁄S.functionFieldClosure).toAffine.Point :=
  (Genuine.base S.prime.EK).domRestrict S.prime.TK

lemma functionFieldTorsionMap_injective : Function.Injective S.functionFieldTorsionMap := by
  intro R T h
  apply Subtype.ext
  exact pointMap_injective S.prime.EK _ h

/-- The generic point is not a disguised constant torsion point. -/
theorem functionFieldGenericPoint_ne_torsion (R : ↥S.prime.TK) :
    S.functionFieldGenericPoint ≠ S.functionFieldTorsionMap R :=
  Genuine.genericPoint_ne_base S.prime.EK R

/-- Function-field automorphisms over the `x`-line fix the embedded global torsion. -/
theorem functionFieldTorsionMap_fixed (σ : Genuine.Gal S.prime.EK) (R : ↥S.prime.TK) :
    Genuine.act S.prime.EK σ (S.functionFieldTorsionMap R) = S.functionFieldTorsionMap R :=
  Genuine.act_base S.prime.EK σ R

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
