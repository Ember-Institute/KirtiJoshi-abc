import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionFields
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionGroups

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Punctured.lean`, function-field identification.
fidelity: identifies the seed's actual base-curve fixed field with the elliptic
function field and embeds it in the same seed's unsigned covering fixed field.
The inclusion preserves the actual ambient embedding and polynomial x coordinate.
boundary: Scene1/Derived. No normalization, etaleness, core, or theta-root identity
is supplied as an assumption or asserted here.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve Polynomial JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

/-- The actual base-curve function field in the seed's geometric ambient closure. -/
def baseCurveFunctionFieldEquiv : S.prime.EK.toAffine.FunctionField ≃+*
    Genuine.stabilizerField S.prime.EK 1 ⊥ false :=
  Genuine.baseFunctionFieldEquiv S.prime.EK

/-- The original curve function field embeds in the seed's actual unsigned covering field. -/
def curveFunctionFieldToCover :
    S.prime.EK.toAffine.FunctionField →+* S.functionFieldCoverField false :=
  (IntermediateField.inclusion (S.functionFieldCoverField_contains_base false)).toRingHom.comp
    S.baseCurveFunctionFieldEquiv.toRingHom

@[simp] theorem coe_curveFunctionFieldToCover (f : S.prime.EK.toAffine.FunctionField) :
    ((S.curveFunctionFieldToCover f : S.functionFieldCoverField false) :
      S.functionFieldClosure) = Genuine.ιF S.prime.EK f := rfl

theorem curveFunctionFieldToCover_injective : Function.Injective S.curveFunctionFieldToCover :=
  S.curveFunctionFieldToCover.injective

/-- The embedding sends the same seed's polynomial coordinate to the genuine generic x value. -/
theorem curveFunctionFieldToCover_algebraMap_poly (p : (↥S.prime.torsionField)[X]) :
    ((S.curveFunctionFieldToCover
      (algebraMap (↥S.prime.torsionField)[X] S.prime.EK.toAffine.FunctionField p) :
      S.functionFieldCoverField false) : S.functionFieldClosure) =
        aeval (Genuine.xG S.prime.EK) p := by
  rw [coe_curveFunctionFieldToCover]
  exact Genuine.ιF_algebraMap_poly S.prime.EK p

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
