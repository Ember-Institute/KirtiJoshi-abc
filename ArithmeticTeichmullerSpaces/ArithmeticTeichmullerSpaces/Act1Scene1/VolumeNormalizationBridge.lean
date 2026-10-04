import ArithmeticTeichmullerSpaces.Act1Scene1.QNormTateBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: JT-ATS-III-SCENE1-VOLUME-NORMALIZATION
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`le:volume-lemma3` (3576--3583), `th:moccor-Mochizuki-form2` (3617--3632),
and `cor:cor312` (3647--3650)
fidelity: Scene1 sign and exponential normalization; the equality between the
target volume and the supplied log-volume is an explicit target condition
boundary: Scene1/Derived

The existing `VolumeTransfer` contract expresses the supplied log-volume as a
sum of packet and hull weights.  This module derives its nonnegativity from
`FirstAxiom`, then consumes an explicit `exp (-logVolume)` normalization to
obtain the target volume side conditions.
-/

structure Corollary312VolumeNormalization
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) : Prop where
  thetaVolume_eq_exp_neg_logVolume :
    T.thetaVolume = Real.exp (-T.scene1.data.link.logVolume)

theorem logVolume_nonneg_of_scene1
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) :
    0 ≤ T.scene1.data.link.logVolume := by
  letI := T.scene1.data.link.packetHull.packetFintype
  letI := T.scene1.data.link.packetHull.hullFintype
  have hFirst := T.scene1.input_laws.first_axiom
  have hPacket :
      0 ≤ ∑ x, T.scene1.data.link.packetHull.packetWeight x := by
    exact Finset.sum_nonneg (fun x hx => (hFirst.packet_weight_positive x).le)
  have hHull :
      0 ≤ ∑ x, T.scene1.data.link.packetHull.hullWeight x := by
    exact Finset.sum_nonneg (fun x hx => (hFirst.hull_weight_positive x).le)
  calc
    0 ≤
        (∑ x, T.scene1.data.link.packetHull.packetWeight x) +
          ∑ x, T.scene1.data.link.packetHull.hullWeight x :=
      add_nonneg hPacket hHull
    _ = T.scene1.data.link.logVolume := by
      symm
      exact T.scene1.volume_transfer.transferred_volume

theorem thetaVolume_pos_of_normalization
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data K O p}
    (N : Corollary312VolumeNormalization p T) :
    0 < T.thetaVolume := by
  rw [N.thetaVolume_eq_exp_neg_logVolume]
  exact Real.exp_pos _

theorem thetaVolume_le_one_of_normalization
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data K O p}
    (N : Corollary312VolumeNormalization p T)
    (hLog : 0 ≤ T.scene1.data.link.logVolume) :
    T.thetaVolume ≤ 1 := by
  rw [N.thetaVolume_eq_exp_neg_logVolume]
  calc
    Real.exp (-T.scene1.data.link.logVolume) ≤ Real.exp 0 := by
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hLog)
    _ = 1 := Real.exp_zero

theorem sideConditions_of_volume_normalization
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (N : Corollary312VolumeNormalization p T)
    (hEllPrime : Nat.Prime T.ell)
    (hEllStarPos : 0 < T.ellStar) :
    Corollary312SideConditions p T := by
  exact
    { ell_prime := hEllPrime
      ellStar_pos := hEllStarPos
      thetaVolume_pos := thetaVolume_pos_of_normalization p N }

theorem corollary312_of_q_family_normalized_lower_bound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312QFamily p T V)
    (N : Corollary312VolumeNormalization p T)
    (hEllPrime : Nat.Prime T.ell)
    (hEllStarPos : 0 < T.ellStar)
    (hLower : T.thetaVolume ≥ Corollary312Data.qProduct p T V.qFactor) :
    Corollary312 p T := by
  have hSide := sideConditions_of_volume_normalization p T N hEllPrime hEllStarPos
  have hLog := logVolume_nonneg_of_scene1 p T
  have hThetaVolume := thetaVolume_le_one_of_normalization p N hLog
  exact corollary312_of_q_family_lower_bound p T hSide V Q hThetaVolume hLower

end JoshiTeich.Act1Scene1
