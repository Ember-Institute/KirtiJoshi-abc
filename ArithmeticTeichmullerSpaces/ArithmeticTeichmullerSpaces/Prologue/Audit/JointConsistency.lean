import ArithmeticTeichmullerSpaces.Prologue.Interfaces
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace JoshiTeich.Prologue.Audit

open JoshiTeich.Prologue
open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-!
source-id: JT-ATS-AUDIT-JOINT-CONSISTENCY
source: mathlib `Mathlib/Data/Fintype/Lattice.lean`, `Finite.exists_max` and
`Finite.exists_min`; contract semantics from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`th:adelic-theta-link` (1139--1166), `def:additive-theta-pilot-object`
(1492--1502), `le:volume-lemma3` (3576--3583), and `cor:cor312`
(3647--3650)
fidelity: derived consistency audit; this is not a new Prologue contract
boundary: Prologue/Audit only

Joint consistency audit for the current Prologue contracts.

The Frobenius square law, positivity, and finiteness force every theta norm to
be `1`.  The log-shell and normalization laws then force the supplied
`logVolume` to be `0`.  Consequently a nonempty positive packet or hull is
incompatible with `VolumeTransfer`.  These are audit conclusions only: no
Core contract is changed here.
-/

theorem theta_norm_eq_one_of_firstAxiom_adelicThetaLink
    (D : AdelicThetaLinkData K)
    (hFirst : FirstAxiom D)
    (hLink : AdelicThetaLink D)
    (hIndex : Nonempty D.theta.index) :
    ∀ i, D.theta.norm i = 1 := by
  letI := D.theta.indexFintype
  letI := hIndex
  classical
  obtain ⟨iMax, hMax⟩ := Finite.exists_max D.theta.norm
  obtain ⟨iMin, hMin⟩ := Finite.exists_min D.theta.norm
  have hMaxPos : 0 < D.theta.norm iMax := hFirst.theta_norm_positive iMax
  have hMinPos : 0 < D.theta.norm iMin := hFirst.theta_norm_positive iMin
  have hMaxSqLe : D.theta.norm iMax ^ 2 ≤ D.theta.norm iMax := by
    calc
      D.theta.norm iMax ^ 2 = D.theta.norm (D.theta.frobenius iMax) := by
        symm
        exact hLink.frobenius_compatibility iMax
      _ ≤ D.theta.norm iMax := hMax (D.theta.frobenius iMax)
  have hMinLeSq : D.theta.norm iMin ≤ D.theta.norm iMin ^ 2 := by
    calc
      D.theta.norm iMin ≤ D.theta.norm (D.theta.frobenius iMin) :=
        hMin (D.theta.frobenius iMin)
      _ = D.theta.norm iMin ^ 2 := hLink.frobenius_compatibility iMin
  have hMaxLeOne : D.theta.norm iMax ≤ 1 := by
    nlinarith
  have hOneLeMin : 1 ≤ D.theta.norm iMin := by
    nlinarith
  intro i
  have hLower : 1 ≤ D.theta.norm i := le_trans hOneLeMin (hMin i)
  have hUpper : D.theta.norm i ≤ 1 := le_trans (hMax i) hMaxLeOne
  exact le_antisymm hUpper hLower

theorem logVolume_eq_zero_of_firstAxiom_adelicThetaLink_thetaLiftLog
    (D : AdelicThetaLinkData K)
    (hFirst : FirstAxiom D)
    (hLink : AdelicThetaLink D)
    (hLog : ThetaLiftLog D)
    (hIndex : Nonempty D.theta.index) :
    D.logVolume = 0 := by
  letI := D.theta.indexFintype
  letI := hIndex
  have hNorm : ∀ i, D.theta.norm i = 1 :=
    theta_norm_eq_one_of_firstAxiom_adelicThetaLink D hFirst hLink hIndex
  rw [hLink.normalization]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hLink.period_map, hLog.log_shell, hNorm i]
  simp

theorem false_of_volumeTransfer_of_nonempty_packet
    (D : AdelicThetaLinkData K)
    (hFirst : FirstAxiom D)
    (hLink : AdelicThetaLink D)
    (hLog : ThetaLiftLog D)
    (hVolume : VolumeTransfer D)
    (hPacket : Nonempty D.packetHull.packet) :
    False := by
  letI := D.packetHull.packetFintype
  letI := D.packetHull.hullFintype
  have hIndex : Nonempty D.theta.index := by
    rcases hPacket with ⟨p⟩
    exact ⟨D.packetHull.packetToPilot p⟩
  have hZero : D.logVolume = 0 :=
    logVolume_eq_zero_of_firstAxiom_adelicThetaLink_thetaLiftLog D hFirst hLink hLog hIndex
  have hPacketSum : 0 < ∑ p, D.packetHull.packetWeight p := by
    exact Finset.sum_pos (fun p hp => hFirst.packet_weight_positive p) Finset.univ_nonempty
  have hHullSum : 0 ≤ ∑ h, D.packetHull.hullWeight h := by
    exact Finset.sum_nonneg (fun h hh => (hFirst.hull_weight_positive h).le)
  rw [hVolume.transferred_volume] at hZero
  nlinarith

theorem false_of_volumeTransfer_of_nonempty_hull
    (D : AdelicThetaLinkData K)
    (hFirst : FirstAxiom D)
    (hLink : AdelicThetaLink D)
    (hLog : ThetaLiftLog D)
    (hVolume : VolumeTransfer D)
    (hHull : Nonempty D.packetHull.hull) :
    False := by
  letI := D.packetHull.packetFintype
  letI := D.packetHull.hullFintype
  have hIndex : Nonempty D.theta.index := by
    rcases hHull with ⟨h⟩
    exact ⟨D.packetHull.packetToPilot (D.packetHull.hullToPacket h)⟩
  have hZero : D.logVolume = 0 :=
    logVolume_eq_zero_of_firstAxiom_adelicThetaLink_thetaLiftLog D hFirst hLink hLog hIndex
  have hPacketSum : 0 ≤ ∑ p, D.packetHull.packetWeight p := by
    exact Finset.sum_nonneg (fun p hp => (hFirst.packet_weight_positive p).le)
  have hHullSum : 0 < ∑ h, D.packetHull.hullWeight h := by
    exact Finset.sum_pos (fun h hh => hFirst.hull_weight_positive h) Finset.univ_nonempty
  rw [hVolume.transferred_volume] at hZero
  nlinarith

end JoshiTeich.Prologue.Audit
