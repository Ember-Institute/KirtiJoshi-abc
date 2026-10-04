import ArithmeticTeichmullerSpaces.Act1Scene1.Corollary312
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: JT-ATS-III-SCENE1-VOLUME-BRIDGE
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`th:moccor-Mochizuki-form2` (3617--3632) and `cor:cor312` (3647--3650)
fidelity: Scene1 analytic bridge; the multiplicative volume bound is an explicit
input and is not promoted to Prologue/Core
boundary: Scene1/Derived

This module proves the logarithmic passage from the multiplicative theta-volume
bound to the exact Corollary 3.12 inequality.  It does not construct the bound
from packet or hull data.
-/

structure Corollary312VolumeData
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  qFactor : T.qIndex → ℝ

structure Corollary312VolumeBound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T) : Prop where
  qFactor_pos : ∀ i, 0 < V.qFactor i
  qFactor_le_one : ∀ i, V.qFactor i ≤ 1
  qLogTerm_eq : ∀ i, T.qLogTerm i = -Real.log (V.qFactor i)
  thetaVolume_le_one : T.thetaVolume ≤ 1
  volume_lower_bound : T.thetaVolume ≥ Corollary312Data.qProduct p T V.qFactor

theorem corollary312_of_volume_lower_bound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hSide : Corollary312SideConditions p T)
    (V : Corollary312VolumeData p T)
    (hBound : Corollary312VolumeBound p T V) :
    Corollary312 p T := by
  letI := T.qIndexFintype
  have hEllStar : 0 < (T.ellStar : ℝ) := Nat.cast_pos.mpr hSide.ellStar_pos
  have hProductPos : 0 < Corollary312Data.qProduct p T V.qFactor := by
    unfold Corollary312Data.qProduct
    exact Finset.prod_pos (fun i hi => pow_pos (hBound.qFactor_pos i) _)
  have hLogLower :
      Real.log (Corollary312Data.qProduct p T V.qFactor) ≤
        Real.log T.thetaVolume :=
    Real.log_le_log hProductPos hBound.volume_lower_bound
  have hLogProduct :
      Real.log (Corollary312Data.qProduct p T V.qFactor) =
        (T.ellStar : ℝ) * ∑ i, Real.log (V.qFactor i) := by
    unfold Corollary312Data.qProduct
    rw [Real.log_prod]
    · simp_rw [Real.log_pow]
      rw [← Finset.mul_sum]
    · intro i hi
      exact pow_ne_zero _ (hBound.qFactor_pos i).ne'
  have hLogScaled :
      ∑ i, Real.log (V.qFactor i) ≤
        (1 / (T.ellStar : ℝ)) * Real.log T.thetaVolume := by
    rw [hLogProduct] at hLogLower
    have hDiv :
        ∑ i, Real.log (V.qFactor i) ≤
          Real.log T.thetaVolume / (T.ellStar : ℝ) := by
      apply (le_div_iff₀ hEllStar).2
      simpa [mul_comm] using hLogLower
    calc
      ∑ i, Real.log (V.qFactor i) ≤
          Real.log T.thetaVolume / (T.ellStar : ℝ) := hDiv
      _ = (1 / (T.ellStar : ℝ)) * Real.log T.thetaVolume := by
        ring
  have hLogVolume_nonpos : Real.log T.thetaVolume ≤ 0 := by
    exact (Real.log_nonpos hSide.thetaVolume_pos.le hBound.thetaVolume_le_one)
  have hAbsLogVolume : |Real.log T.thetaVolume| = -Real.log T.thetaVolume :=
    abs_of_nonpos hLogVolume_nonpos
  change -(1 / (T.ellStar : ℝ)) * |Real.log T.thetaVolume| ≥
    -Corollary312Data.qLogSum p T
  rw [hAbsLogVolume]
  have hQLogSum :
      Corollary312Data.qLogSum p T =
        -∑ i, Real.log (V.qFactor i) := by
    unfold Corollary312Data.qLogSum
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hBound.qLogTerm_eq i
  rw [hQLogSum]
  nlinarith [hLogScaled]

end JoshiTeich.Act1Scene1
