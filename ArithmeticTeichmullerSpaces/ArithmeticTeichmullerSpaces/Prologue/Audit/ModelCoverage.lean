import ArithmeticTeichmullerSpaces.Prologue.Audit.Models
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidBridgeModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.InputModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.TateModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.PilotModels

namespace JoshiTeich.Prologue.Audit

/-!
The model matrix records one compiled satisfying and violating witness for each
Prologue law interface.  Arithmetic profiles are Type carriers whose
non-negativity and divisor conditions are fields, so they receive explicit
model-obligation entries instead of fabricated counterexamples.
-/

open JoshiTeich.Prologue.Arithmetic

def satisfyingModelIds : List String :=
  [ "FirstAxiom"
  , "AdelicThetaLink"
  , "ThetaLiftLog"
  , "PacketCollationHull"
  , "VolumeTransfer"
  , "TateParameterLaws"
  , "ThetaPilotScalingLaws"
  , "PerfectoidLaws"
  , "PerfectoidBridgeLaws"
  , "PrologueInputLaws" ]

def violatingModelIds : List String := satisfyingModelIds

def modelObligationIds : List String :=
  [ "FinitePlaceDivisor"
  , "HeightData"
  , "RamificationProfile" ]

theorem satisfyingModelIds_count : satisfyingModelIds.length = 10 := by
  rfl

theorem violatingModelIds_count : violatingModelIds.length = 10 := by
  rfl

theorem modelObligationIds_count : modelObligationIds.length = 3 := by
  rfl

-- Satisfying witnesses.
#check firstAxiom_model
#check adelicThetaLink_model
#check thetaLiftLog_model
#check packetCollationHull_model
#check volumeTransfer_model
#check auditTateData_laws
#check auditScalingTheta_laws
#check padicTwo_perfectoid_model
#check padicTwo_bridge_model
#check padicTwo_input_laws

-- Violating witnesses.
#check firstAxiom_violation
#check adelicThetaLink_violation
#check thetaLiftLog_violation
#check packetCollationHull_violation
#check volumeTransfer_violation
#check auditTateData_violation
#check zeroScalingTheta_violates_laws
#check zeroPerfectoidData_violates_laws
#check zero_bridge_violates_laws
#check badInput_violates_laws

-- Type-level arithmetic invariants are checked by their constructors.
#check FinitePlaceDivisor.exponent_ne_zero
#check HeightData.weight_nonneg
#check HeightData.value_eq
#check RamificationProfile.different_log_nonneg
#check RamificationProfile.conductor_log_nonneg

end JoshiTeich.Prologue.Audit
