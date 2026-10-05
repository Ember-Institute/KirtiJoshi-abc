import ArithmeticTeichmullerSpaces.Prologue.Arithmetic
import ArithmeticTeichmullerSpaces.Prologue.Perfectoid
import ArithmeticTeichmullerSpaces.Prologue.Theta
import ArithmeticTeichmullerSpaces.Prologue.Interfaces
import ArithmeticTeichmullerSpaces.Prologue.Audit.FieldCoverage
import ArithmeticTeichmullerSpaces.Prologue.Audit.ModelCoverage
import ArithmeticTeichmullerSpaces.Prologue.Audit.Models
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidBridgeModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.InputModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.TateModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.PilotModels
import ArithmeticTeichmullerSpaces.Prologue.Audit.JointConsistency
import ArithmeticTeichmullerSpaces.Act1Scene1.Audit.Models

namespace JoshiTeich.Prologue.Audit

/-!
This module is the compile-time import audit for the public Prologue surface.
The checks below name every public carrier, contract, and model entry point.
The `Obligations` namespace is intentionally absent from this import graph.
-/

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open JoshiTeich.Prologue.Theta
open scoped NumberField

-- Public carriers and arithmetic profiles.
#check ThetaPilotData
#check PacketHullData
#check AdelicThetaLinkData
#check Arithmetic.FinitePlaceDivisor
#check Arithmetic.HeightData
#check Arithmetic.RamificationProfile

-- Public Perfectoid and input boundaries.
#check Perfectoid.PerfectoidData
#check Perfectoid.PerfectoidLaws
#check PerfectoidPlaceData
#check PerfectoidBridgeData
#check PrologueInputData

-- Public Prologue contracts.
#check FirstAxiom
#check AdelicThetaLink
#check ThetaLiftLog
#check PacketCollationHull
#check VolumeTransfer
#check PrologueInputLaws

-- Satisfying and violating model witnesses.
#check auditData
#check firstAxiom_model
#check firstAxiom_violation
#check adelicThetaLink_model
#check adelicThetaLink_violation
#check thetaLiftLog_model
#check thetaLiftLog_violation
#check packetCollationHull_model
#check packetCollationHull_violation
#check volumeTransfer_model
#check volumeTransfer_violation
#check padicTwo_perfectoid_model
#check zeroPerfectoidData_violates_laws
#check padicTwo_bridge_model
#check zero_bridge_violates_laws
#check padicTwo_input_laws
#check badInput_violates_laws
#check auditTateData_laws
#check auditTateData_violation
#check auditScalingTheta_laws
#check zeroScalingTheta_violates_laws
#check theta_norm_eq_one_of_firstAxiom_frobeniusSquareCandidate
#check logVolume_eq_zero_of_firstAxiom_frobeniusSquareCandidate_thetaLiftLog
#check false_of_volumeTransfer_of_nonempty_packet_with_frobeniusSquareCandidate
#check false_of_volumeTransfer_of_nonempty_hull_with_frobeniusSquareCandidate

-- Scene1 joint models: one satisfying witness and one normalization countermodel.
#check JoshiTeich.Act1Scene1.Audit.sceneInput
#check JoshiTeich.Act1Scene1.Audit.scene_satisfying_model
#check JoshiTeich.Act1Scene1.Audit.scene_bad_normalization_violation

end JoshiTeich.Prologue.Audit
