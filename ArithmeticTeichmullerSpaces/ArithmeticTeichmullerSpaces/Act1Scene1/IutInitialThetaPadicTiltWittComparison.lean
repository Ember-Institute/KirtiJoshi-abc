import ArithmeticTeichmullerSpaces.Act1Scene1.WittRingEquiv
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedMapPower
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicTiltTopology

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-TILT-WITT-COMPARISON
source: Joshi II `se:ff-rings`, integral Witt vectors of the fixed tilt;
the proved actual-to-standard tilt integer-ring comparison.
fidelity: constructs a ring equivalence between Witt vectors of the actual
tilt integers and of the independent standard C_p tilt integers. The
coefficient, Teichmuller, and Frobenius formulas use the same integer-ring
equivalence, and extends it to the localization obtained by inverting p.
The field-Witt comparison retains the original norms and proves
V_standard(rho, e(x))^localDeg = V_actual(rho^localDeg, x).
No comparison certificate is added. Localization at a contracting Teichmuller
element, rho completion, and paper B identity remain open.
Original proofs; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicTiltWittComparison

open JoshiTeich.Prologue
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

-- Inferring the complete result type preserves the coefficient-ring instances
-- of the proved integer equivalence, including the standard localization.
def integerWittEquiv := WittRingEquiv.mapEquiv (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.integerEquiv D w)

theorem integerWittEquiv_coeff
    (x : WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltIntegers.Integers D w))
    (n : ℕ) :
    (integerWittEquiv D w x).coeff n =
      InitialThetaPadicTiltTopology.integerEquiv D w (x.coeff n) :=
  WittRingEquiv.mapEquiv_coeff (Arithmetic.residueChar w.1)
    (InitialThetaPadicTiltTopology.integerEquiv D w) x n

theorem integerWittEquiv_teichmuller (x : InitialThetaTiltIntegers.Integers D w) :
    integerWittEquiv D w (WittVector.teichmuller (Arithmetic.residueChar w.1) x) =
      WittVector.teichmuller (Arithmetic.residueChar w.1)
        (InitialThetaPadicTiltTopology.integerEquiv D w x) :=
  WittRingEquiv.mapEquiv_teichmuller (Arithmetic.residueChar w.1)
    (InitialThetaPadicTiltTopology.integerEquiv D w) x

theorem integerWittEquiv_frobenius
    (x : WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltIntegers.Integers D w)) :
    integerWittEquiv D w (WittVector.frobenius x) =
      WittVector.frobenius (integerWittEquiv D w x) :=
  WittRingEquiv.mapEquiv_frobenius (Arithmetic.residueChar w.1)
    (InitialThetaPadicTiltTopology.integerEquiv D w) x

def invertPrimeEquiv := WittRingEquiv.invertPrimeEquiv (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.integerEquiv D w)

-- Infer the localization instances from the generic compatibility statement.
theorem invertPrimeEquiv_algebraMap
    (x : WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltIntegers.Integers D w)) :
    invertPrimeEquiv D w (algebraMap _ _ x) =
      algebraMap _ _ (integerWittEquiv D w x) :=
  WittRingEquiv.invertPrimeEquiv_algebraMap (Arithmetic.residueChar w.1)
    (InitialThetaPadicTiltTopology.integerEquiv D w) x

local instance actualRawField : Field (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltField.carrierField D w
local instance standardRawField : Field (InitialThetaPadicTiltTopology.Standard D w) :=
  FractionRing.field (PadicTiltField.Source (Arithmetic.residueChar w.1))
local instance actualNormedField : NormedField (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltTopology.carrierNormedField D w
local instance standardNormedField : NormedField (InitialThetaPadicTiltTopology.Standard D w) :=
  PadicTiltField.carrierNormedField (Arithmetic.residueChar w.1)

def fieldWittEquiv := WittWeightedMapPower.mapEquiv (Arithmetic.residueChar w.1)
  (InitialThetaPadicTiltTopology.ringEquiv D w)

section InferredProofs
-- These proof-valued definitions retain the complete inferred specialization types.
set_option linter.defProp false

private def coefficientNormPower := InitialThetaPadicTiltTopology.norm_pow D w

private def weightedValueTransfer :=
  WittWeightedMapPower.value_mapEquiv_pow (Arithmetic.residueChar w.1)
    (InitialThetaPadicTiltTopology.ringEquiv D w)

-- V_standard(rho, fieldWittEquiv(x))^d = V_actual(rho^d, x), d = localDeg(w).
def fieldWittEquiv_value_pow :=
  weightedValueTransfer D w (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1) (coefficientNormPower D w)

end InferredProofs

end
end JoshiTeich.Act1Scene1.InitialThetaPadicTiltWittComparison
