import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceIndexBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-TRANSFER
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` and
`refer/iut/Iut/Cor312/ThetaRegion.lean`; target-side accounting:
`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`pr:general-cohomology-set-const` (3261--3271), `th:thetam-construction`
(3296--3346), `le:volume-lemma3` (3576--3583), and `cor:cor312`
(3647--3650)
fidelity: consumes the adapted q-pilot global sum in the packet/hull transfer
bound; all source constructions and normalization identifications remain
explicit Scene1 inputs
boundary: Scene1/Derived

The q-pilot bridge is useful only when it reaches the transfer estimate.  The
`transfer_log_bound` field below is the target-equivalent core estimate in
q-pilot notation, once its source normalization and index bridge identify
`P.absLogQ` with the target q-log sum; the field is not a proof of that estimate.
This module can derive it from explicit accounting, normalization, and
source-index inputs, then assemble the conditional Corollary 3.12 result without
adding q-pilot data to Prologue/Core.
-/

namespace Corollary312TateQFamily

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {V : Corollary312VolumeData p T}

/-- The target q-log sum and the grouped source q-log sum are the same finite
sum after the q-family's explicit grouping equivalence. -/
theorem qLogSum_eq_sourceQLogSum
    (Q : Corollary312TateQFamily p T V) :
    Corollary312Data.qLogSum p T = Corollary312SourceQLogSum p T V Q := by
  letI := T.qIndexFintype
  letI := Q.grouping.pairFintype
  unfold Corollary312Data.qLogSum Corollary312SourceQLogSum
  calc
    (∑ i : T.qIndex, T.qLogTerm i) =
        ∑ i : T.qIndex,
          -Real.log (Corollary312GroupedSourceQFactor p T Q.grouping
            (Q.grouping.indexEquiv i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Q.qLogTerm_eq]
      rw [← Q.grouping_place_eq i]
      rfl
    _ = ∑ a : Q.grouping.pair,
          -Real.log (Corollary312GroupedSourceQFactor p T Q.grouping a) := by
      simpa using Q.grouping.indexEquiv.sum_comp
        (fun a => -Real.log (Corollary312GroupedSourceQFactor p T Q.grouping a))

end Corollary312TateQFamily

structure Corollary312QPilotTransferLogBound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (P : Corollary312QPilotData p T) : Prop where
  /-- Core target-equivalent estimate in q-pilot notation. -/
  transfer_log_bound :
    Corollary312PacketWeightSum p T + Corollary312HullWeightSum p T ≤
      (T.ellStar : ℝ) * P.absLogQ p

theorem transferLogBound_of_tateQAccounting_qPilot
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312TateQFamily p T V)
    (A : Corollary312TateQAccounting p T V Q)
    (P : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312QPilotSourceNormalization p T hOrder P)
    (hEll : 0 < T.ell)
    (B : Corollary312QPilotSourceIndexBridge p T V P Q) :
    Corollary312QPilotTransferLogBound p T P := by
  letI := T.scene1.data.link.packetHull.packetFintype
  letI := T.scene1.data.link.packetHull.hullFintype
  have hPacket :
      Corollary312PacketWeightSum p T ≤
        Corollary312PacketSourceQLogSum p T V Q A.packet_pair := by
    unfold Corollary312PacketWeightSum Corollary312PacketSourceQLogSum
    exact Finset.sum_le_sum (fun x hx => A.packet_weight_le_source_qLogTerm x)
  have hHull :
      Corollary312HullWeightSum p T ≤
        Corollary312HullSourceQLogSum p T V Q A.hull_pair := by
    unfold Corollary312HullWeightSum Corollary312HullSourceQLogSum
    exact Finset.sum_le_sum (fun x hx => A.hull_weight_le_source_qLogTerm x)
  have hAccounting :
      Corollary312PacketSourceQLogSum p T V Q A.packet_pair +
          Corollary312HullSourceQLogSum p T V Q A.hull_pair =
        (T.ellStar : ℝ) * P.absLogQ p := by
    calc
      Corollary312PacketSourceQLogSum p T V Q A.packet_pair +
          Corollary312HullSourceQLogSum p T V Q A.hull_pair =
        (T.ellStar : ℝ) * Corollary312SourceQLogSum p T V Q :=
          A.q_accounting
      _ = (T.ellStar : ℝ) * P.absLogQ p := by
        rw [Corollary312QPilotSourceIndexBridge.absLogQ_eq_sourceQLogSum
          (p := p) (T := T) (V := V) (P := P) (Q := Q)
          hOrder hNorm hEll B]
  exact
    { transfer_log_bound := by
        calc
          Corollary312PacketWeightSum p T + Corollary312HullWeightSum p T ≤
              Corollary312PacketSourceQLogSum p T V Q A.packet_pair +
                Corollary312HullSourceQLogSum p T V Q A.hull_pair :=
            add_le_add hPacket hHull
          _ = (T.ellStar : ℝ) * P.absLogQ p := hAccounting }

theorem transferLogBound_of_qPilotTransferLogBound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312TateQFamily p T V)
    (P : Corollary312QPilotData p T)
    (L : Corollary312QPilotTransferLogBound p T P)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312QPilotSourceNormalization p T hOrder P)
    (hEll : 0 < T.ell)
    (B : Corollary312QPilotSourceIndexBridge p T V P Q) :
    Corollary312TransferLogBound p T := by
  exact
    { transfer_log_bound := by
        calc
          Corollary312PacketWeightSum p T + Corollary312HullWeightSum p T ≤
              (T.ellStar : ℝ) * P.absLogQ p := L.transfer_log_bound
          _ = (T.ellStar : ℝ) * Corollary312SourceQLogSum p T V Q := by
            rw [Corollary312QPilotSourceIndexBridge.absLogQ_eq_sourceQLogSum
              (p := p) (T := T) (V := V) (P := P) (Q := Q)
              hOrder hNorm hEll B]
          _ = (T.ellStar : ℝ) * Corollary312Data.qLogSum p T := by
            rw [Corollary312TateQFamily.qLogSum_eq_sourceQLogSum p Q] }

theorem corollary312_of_qPilot_accounting
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312TateQFamily p T V)
    (N : Corollary312VolumeNormalization p T)
    (A : Corollary312TateQAccounting p T V Q)
    (P : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312QPilotSourceNormalization p T hOrder P)
    (hEll : 0 < T.ell)
    (B : Corollary312QPilotSourceIndexBridge p T V P Q)
    (hEllPrime : Nat.Prime T.ell)
    (hEllGeFive : 5 ≤ T.ell)
    (hEllStarEq : T.ellStar = (T.ell - 1) / 2)
    (hEllStarPos : 0 < T.ellStar) :
    Corollary312 p T := by
  have hPilot := transferLogBound_of_tateQAccounting_qPilot p T V Q A P
    hOrder hNorm hEll B
  exact corollary312_of_transfer_log_bound p T V Q.toQFamily N
    (transferLogBound_of_qPilotTransferLogBound p T V Q P hPilot
      hOrder hNorm hEll B)
    hEllPrime hEllGeFive hEllStarEq hEllStarPos

end JoshiTeich.Act1Scene1
