import ArithmeticTeichmullerSpaces.Act1Scene1.VolumeNormalizationBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: JT-ATS-III-SCENE1-TRANSFER-Q-LOWER
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`le:volume-lemma3` (3576--3583), `th:moccor-Mochizuki-form2` (3617--3632),
and `cor:cor312` (3647--3650)
fidelity: Scene1 bridge from a packet/hull finite-sum estimate to the
multiplicative theta-volume lower bound; the finite-sum estimate remains an
explicit derived input
boundary: Scene1/Derived

The estimate is stated against the actual packet and hull weight sums, so
`VolumeTransfer` is consumed by a separate rewriting theorem.  The module then
performs the logarithm/exponential passage to the q-product.
-/

def Corollary312PacketWeightSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) : ℝ :=
  letI := T.scene1.data.link.packetHull.packetFintype
  ∑ x, T.scene1.data.link.packetHull.packetWeight x

def Corollary312HullWeightSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) : ℝ :=
  letI := T.scene1.data.link.packetHull.hullFintype
  ∑ x, T.scene1.data.link.packetHull.hullWeight x

structure Corollary312TransferLogBound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) : Prop where
  transfer_log_bound :
    Corollary312PacketWeightSum p T + Corollary312HullWeightSum p T ≤
      (T.ellStar : ℝ) * Corollary312Data.qLogSum p T

theorem logVolume_upper_bound_of_transfer_log_bound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (L : Corollary312TransferLogBound p T) :
    T.scene1.data.link.logVolume ≤
      (T.ellStar : ℝ) * Corollary312Data.qLogSum p T := by
  letI := T.scene1.data.link.packetHull.packetFintype
  letI := T.scene1.data.link.packetHull.hullFintype
  calc
    T.scene1.data.link.logVolume =
        (∑ x, T.scene1.data.link.packetHull.packetWeight x) +
          ∑ x, T.scene1.data.link.packetHull.hullWeight x :=
      T.scene1.volume_transfer.transferred_volume
    _ ≤ (T.ellStar : ℝ) * Corollary312Data.qLogSum p T := by
      simpa [Corollary312PacketWeightSum, Corollary312HullWeightSum] using
        L.transfer_log_bound

theorem thetaVolume_lower_bound_of_transfer_log_bound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312QFamily p T V)
    (N : Corollary312VolumeNormalization p T)
    (L : Corollary312TransferLogBound p T) :
    T.thetaVolume ≥ Corollary312Data.qProduct p T V.qFactor := by
  letI := T.qIndexFintype
  have hQPos : ∀ i, 0 < V.qFactor i :=
    Corollary312QFamily.qFactor_pos p Q
  have hQLogSum :
      Corollary312Data.qLogSum p T = -∑ i, Real.log (V.qFactor i) := by
    unfold Corollary312Data.qLogSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Corollary312QFamily.qLogTerm_source p Q i
  have hLogUpper := logVolume_upper_bound_of_transfer_log_bound p T L
  rw [hQLogSum] at hLogUpper
  have hLogNeg :
      (T.ellStar : ℝ) * ∑ i, Real.log (V.qFactor i) ≤
        -T.scene1.data.link.logVolume := by
    nlinarith [hLogUpper]
  have hProductPos : 0 < Corollary312Data.qProduct p T V.qFactor := by
    unfold Corollary312Data.qProduct
    exact Finset.prod_pos (fun i hi => pow_pos (hQPos i) _)
  have hLogProduct :
      Real.log (Corollary312Data.qProduct p T V.qFactor) =
        (T.ellStar : ℝ) * ∑ i, Real.log (V.qFactor i) := by
    unfold Corollary312Data.qProduct
    rw [Real.log_prod]
    · simp_rw [Real.log_pow]
      rw [← Finset.mul_sum]
    · intro i hi
      exact pow_ne_zero _ (hQPos i).ne'
  have hExpProduct :
      Real.exp ((T.ellStar : ℝ) * ∑ i, Real.log (V.qFactor i)) =
        Corollary312Data.qProduct p T V.qFactor := by
    rw [← hLogProduct]
    exact Real.exp_log hProductPos
  calc
    Corollary312Data.qProduct p T V.qFactor =
        Real.exp ((T.ellStar : ℝ) * ∑ i, Real.log (V.qFactor i)) :=
      hExpProduct.symm
    _ ≤ Real.exp (-T.scene1.data.link.logVolume) :=
      Real.exp_le_exp.mpr hLogNeg
    _ = T.thetaVolume := N.thetaVolume_eq_exp_neg_logVolume.symm

theorem corollary312_of_transfer_log_bound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312QFamily p T V)
    (N : Corollary312VolumeNormalization p T)
    (L : Corollary312TransferLogBound p T)
    (hEllPrime : Nat.Prime T.ell)
    (hEllGeFive : 5 ≤ T.ell)
    (hEllStarEq : T.ellStar = (T.ell - 1) / 2)
    (hEllStarPos : 0 < T.ellStar) :
    Corollary312 p T := by
  have hLower := thetaVolume_lower_bound_of_transfer_log_bound p T V Q N L
  exact corollary312_of_q_family_normalized_lower_bound
    p T V Q N hEllPrime hEllGeFive hEllStarEq hEllStarPos hLower

end JoshiTeich.Act1Scene1
