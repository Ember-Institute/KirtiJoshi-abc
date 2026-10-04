import ArithmeticTeichmullerSpaces.Act1Scene1.TransferQLowerBound

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: JT-ATS-III-SCENE1-TRANSFER-Q-ACCOUNTING
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`pr:general-cohomology-set-const` (3261--3271),
`th:thetam-construction` (3296--3346), `le:volume-lemma3` (3576--3583),
and `cor:cor312` (3647--3650)
fidelity: Scene1 component accounting for packet/hull weights and q terms;
the packet/hull maps, pointwise estimates, and finite accounting equality are
explicit construction obligations
boundary: Scene1/Derived

This module makes the finite-sum estimate auditable at component level.  It
does not claim that the paper's packet construction has already been realized
by the Prologue carriers.
-/

def Corollary312PacketQLogSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (f : T.scene1.data.link.packetHull.packet → T.qIndex) : ℝ :=
  letI := T.scene1.data.link.packetHull.packetFintype
  ∑ x, T.qLogTerm (f x)

def Corollary312HullQLogSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (f : T.scene1.data.link.packetHull.hull → T.qIndex) : ℝ :=
  letI := T.scene1.data.link.packetHull.hullFintype
  ∑ x, T.qLogTerm (f x)

structure Corollary312TransferQAccounting
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  packet_qIndex : T.scene1.data.link.packetHull.packet → T.qIndex
  hull_qIndex : T.scene1.data.link.packetHull.hull → T.qIndex
  packet_weight_le_qLogTerm :
    ∀ x, T.scene1.data.link.packetHull.packetWeight x ≤
      T.qLogTerm (packet_qIndex x)
  hull_weight_le_qLogTerm :
    ∀ x, T.scene1.data.link.packetHull.hullWeight x ≤
      T.qLogTerm (hull_qIndex x)
  q_accounting :
    Corollary312PacketQLogSum p T packet_qIndex +
        Corollary312HullQLogSum p T hull_qIndex =
      (T.ellStar : ℝ) * Corollary312Data.qLogSum p T

theorem transferLogBound_of_qAccounting
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (A : Corollary312TransferQAccounting p T) :
    Corollary312TransferLogBound p T := by
  letI := T.scene1.data.link.packetHull.packetFintype
  letI := T.scene1.data.link.packetHull.hullFintype
  have hPacket :
      Corollary312PacketWeightSum p T ≤
        Corollary312PacketQLogSum p T A.packet_qIndex := by
    unfold Corollary312PacketWeightSum Corollary312PacketQLogSum
    exact Finset.sum_le_sum (fun x hx => A.packet_weight_le_qLogTerm x)
  have hHull :
      Corollary312HullWeightSum p T ≤
        Corollary312HullQLogSum p T A.hull_qIndex := by
    unfold Corollary312HullWeightSum Corollary312HullQLogSum
    exact Finset.sum_le_sum (fun x hx => A.hull_weight_le_qLogTerm x)
  exact
    { transfer_log_bound := by
        calc
          Corollary312PacketWeightSum p T + Corollary312HullWeightSum p T ≤
              Corollary312PacketQLogSum p T A.packet_qIndex +
                Corollary312HullQLogSum p T A.hull_qIndex :=
            add_le_add hPacket hHull
          _ = (T.ellStar : ℝ) * Corollary312Data.qLogSum p T :=
            A.q_accounting }

theorem corollary312_of_transfer_q_accounting
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312QFamily p T V)
    (N : Corollary312VolumeNormalization p T)
    (A : Corollary312TransferQAccounting p T)
    (hEllPrime : Nat.Prime T.ell)
    (hEllStarPos : 0 < T.ellStar) :
    Corollary312 p T := by
  exact corollary312_of_transfer_log_bound p T V Q N
    (transferLogBound_of_qAccounting p T A) hEllPrime hEllStarPos

end JoshiTeich.Act1Scene1
