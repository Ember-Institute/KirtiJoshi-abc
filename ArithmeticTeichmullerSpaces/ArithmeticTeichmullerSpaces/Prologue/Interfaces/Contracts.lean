import ArithmeticTeichmullerSpaces.Prologue.Interfaces.Carriers
import ArithmeticTeichmullerSpaces.Prologue.Theta.Pilot
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace JoshiTeich.Prologue

open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-! The first-axiom contract records non-degenerate input conditions. -/
structure FirstAxiom (D : AdelicThetaLinkData K) : Prop where
  places_nonempty : D.places.Nonempty
  q_parameter_nonzero : D.qParameter ≠ 0
  q_norm_positive : ∀ w ∈ D.places, 0 < D.qNorm w
  height_nonnegative : ∀ x, 0 ≤ D.height x
  theta_norm_positive : ∀ i, 0 < D.theta.norm i
  packet_weight_positive : ∀ p, 0 < D.packetHull.packetWeight p
  hull_weight_positive : ∀ h, 0 < D.packetHull.hullWeight h

/-! Local-to-global theta-link relations.  No global volume inequality appears here. -/
structure AdelicThetaLink (D : AdelicThetaLinkData K) : Prop where
  valuation_scaling :
    ∀ w ∈ D.places, ∀ j : ℕ,
      D.qNorm w ^ (j * j) = w (D.qParameter ^ (j * j))
  theta_scaling :
    Theta.ThetaPilotScalingLaws D.theta D.thetaBase
  period_map :
    ∀ i, D.theta.period i = D.theta.liftedLog i
  normalization :
    letI := D.theta.indexFintype
    D.logVolume = ∑ i, D.theta.period i

/-! The lifted log-shell relation is kept separate from the theta-link itself. -/
structure ThetaLiftLog (D : AdelicThetaLinkData K) : Prop where
  log_shell : ∀ i, D.theta.liftedLog i = Real.log (D.theta.norm i)
  value_nonzero : ∀ i, D.theta.value i ≠ 0

/-! Finite packet and hull collation relations. -/
structure PacketCollationHull (D : AdelicThetaLinkData K) : Prop where
  packet_supported : ∀ p, D.packetHull.packetToPilot p ∈ D.thetaIndices
  hull_supported : ∀ h, D.packetHull.hullToPacket h ∈ D.packetIndices
  packet_weights_nonzero : ∀ p, D.packetHull.packetWeight p ≠ 0
  hull_weights_nonzero : ∀ h, D.packetHull.hullWeight h ≠ 0

/-! The volume-transfer contract only relates finite sums of supplied data. -/
structure VolumeTransfer (D : AdelicThetaLinkData K) : Prop where
  transferred_volume :
    letI := D.packetHull.packetFintype
    letI := D.packetHull.hullFintype
    D.logVolume =
      (∑ p, D.packetHull.packetWeight p) +
        ∑ h, D.packetHull.hullWeight h

end JoshiTeich.Prologue
