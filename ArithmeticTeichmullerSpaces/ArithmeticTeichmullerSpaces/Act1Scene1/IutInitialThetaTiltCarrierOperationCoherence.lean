import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicTiltTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.RingEquivDictionaryTransport

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-CARRIER-OPERATION-COHERENCE
source: Joshi II `se:ff-rings`, the actual tilt field comparison.
fidelity: extracts the source operations of the original field equivalence
and compares them with the original actual normed-field operations.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
boundary: these identities do not construct or replace an equivalence.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltCarrierOperationCoherence

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def sourceMul : Mul (InitialThetaTiltField.Carrier D w) :=
  RingEquivDictionaryTransport.sourceMul (InitialThetaPadicTiltTopology.ringEquiv D w)

def sourceAdd : Add (InitialThetaTiltField.Carrier D w) :=
  RingEquivDictionaryTransport.sourceAdd (InitialThetaPadicTiltTopology.ringEquiv D w)

def normedMul : Mul (InitialThetaTiltField.Carrier D w) := by
  letI localNF : NormedField (InitialThetaTiltField.Carrier D w) :=
    InitialThetaTiltTopology.carrierNormedField D w
  exact inferInstance

def normedAdd : Add (InitialThetaTiltField.Carrier D w) := by
  letI localNF : NormedField (InitialThetaTiltField.Carrier D w) :=
    InitialThetaTiltTopology.carrierNormedField D w
  exact inferInstance

theorem sourceMul_eq_normedMul : sourceMul D w = normedMul D w := rfl

theorem sourceAdd_eq_normedAdd : sourceAdd D w = normedAdd D w := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaTiltCarrierOperationCoherence
