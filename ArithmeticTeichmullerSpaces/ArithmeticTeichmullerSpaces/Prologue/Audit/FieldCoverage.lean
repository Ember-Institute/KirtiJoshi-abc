import ArithmeticTeichmullerSpaces.Prologue.Arithmetic
import ArithmeticTeichmullerSpaces.Prologue.Perfectoid
import ArithmeticTeichmullerSpaces.Prologue.Theta
import ArithmeticTeichmullerSpaces.Prologue.Interfaces

namespace JoshiTeich.Prologue.Audit

/-!
Projection checks for the source ledger's field-level coverage.  These checks
make a renamed or removed public field fail the audit at compile time.
-/

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open JoshiTeich.Prologue.Perfectoid
open JoshiTeich.Prologue.Theta

-- Carrier fields.
#check ThetaPilotData.index
#check ThetaPilotData.indexFintype
#check ThetaPilotData.value
#check ThetaPilotData.norm
#check ThetaPilotData.scalingIndex
#check ThetaPilotData.frobenius
#check ThetaPilotData.period
#check ThetaPilotData.liftedLog
#check PacketHullData.packet
#check PacketHullData.packetFintype
#check PacketHullData.packetToPilot
#check PacketHullData.packetWeight
#check PacketHullData.hull
#check PacketHullData.hullFintype
#check PacketHullData.hullToPacket
#check PacketHullData.hullWeight
#check AdelicThetaLinkData.places
#check AdelicThetaLinkData.qParameter
#check AdelicThetaLinkData.tate
#check AdelicThetaLinkData.theta
#check AdelicThetaLinkData.thetaBase
#check AdelicThetaLinkData.packetHull
#check AdelicThetaLinkData.heightData
#check AdelicThetaLinkData.ramification
#check AdelicThetaLinkData.logVolume
#check AdelicThetaLinkData.processionLength

-- Arithmetic profile fields.
#check Arithmetic.FinitePlaceDivisor.support
#check Arithmetic.FinitePlaceDivisor.exponent
#check Arithmetic.FinitePlaceDivisor.exponent_ne_zero
#check Arithmetic.HeightData.places
#check Arithmetic.HeightData.weight
#check Arithmetic.HeightData.weight_nonneg
#check Arithmetic.HeightData.value
#check Arithmetic.HeightData.value_eq
#check Arithmetic.RamificationProfile.conductor
#check Arithmetic.RamificationProfile.different_log
#check Arithmetic.RamificationProfile.conductor_log
#check Arithmetic.RamificationProfile.different_log_nonneg
#check Arithmetic.RamificationProfile.conductor_log_nonneg

-- Perfectoid and Tate fields.
#check Perfectoid.UntiltingLaws.one
#check Perfectoid.UntiltingLaws.reduction
#check Perfectoid.UntiltingLaws.frobenius_scaling
#check Perfectoid.FontaineThetaLaws.teichmuller
#check Perfectoid.PerfectoidData.untilt
#check Perfectoid.PerfectoidData.theta
#check Perfectoid.PerfectoidLaws.untilting
#check Perfectoid.PerfectoidLaws.theta_compatibility
#check TateParameterData.places
#check TateParameterData.parameter
#check TateParameterData.norm
#check TateParameterData.orderNat
#check TateParameterLaws.places_nonempty
#check TateParameterLaws.parameter_nonzero
#check TateParameterLaws.norm_eq
#check TateParameterLaws.norm_pos
#check TateParameterLaws.norm_lt_one
#check TateParameterLaws.orderNat_pos
#check ThetaPilotScalingLaws.base_scalingIndex
#check ThetaPilotScalingLaws.value_nonzero
#check ThetaPilotScalingLaws.norm_positive
#check ThetaPilotScalingLaws.norm_scaling

-- Bridge and bundled input fields.
#check PerfectoidPlaceData.place
#check PerfectoidPlaceData.data
#check PerfectoidPlaceLaws.perfectoid
#check PerfectoidBridgeData.coefficientMap
#check PerfectoidBridgeLaws.place_supported
#check PerfectoidBridgeLaws.local_laws
#check PrologueInputData.link
#check PrologueInputData.placeData
#check PrologueInputData.bridge
#check PrologueInputLaws.first_axiom
#check PrologueInputLaws.tate_parameter
#check PrologueInputLaws.adelic_theta_link
#check PrologueInputLaws.perfectoid_bridge

-- Contract fields.
#check FirstAxiom.places_nonempty
#check FirstAxiom.q_parameter_nonzero
#check FirstAxiom.q_norm_positive
#check FirstAxiom.height_nonnegative
#check FirstAxiom.theta_norm_positive
#check FirstAxiom.packet_weight_positive
#check FirstAxiom.hull_weight_positive
#check AdelicThetaLink.valuation_scaling
#check AdelicThetaLink.theta_scaling
#check AdelicThetaLink.period_map
#check AdelicThetaLink.normalization
#check ThetaLiftLog.log_shell
#check ThetaLiftLog.value_nonzero
#check PacketCollationHull.packet_supported
#check PacketCollationHull.hull_supported
#check PacketCollationHull.packet_weights_nonzero
#check PacketCollationHull.hull_weights_nonzero
#check VolumeTransfer.transferred_volume

end JoshiTeich.Prologue.Audit
