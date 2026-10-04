import ArithmeticTeichmullerSpaces.Prologue.Interfaces
import Mathlib.NumberTheory.NumberField.Basic

namespace JoshiTeich.Prologue.Audit

open JoshiTeich.Prologue
open scoped BigOperators NumberField

/-!
Concrete model checks for the Prologue contracts.

The models use `ℚ`, its actual ring of integers, and the finite place induced
by the prime ideal over `2`.  The numerical values are deliberately visible:
the parameter is `2`, the pilot value is `2`, packet and hull weights are `2`
and `3`, and the log-volume is varied per contract.  This prevents the audit
from passing only because every field is `0` or `1`.
-/

noncomputable def rationalTwoPrimeIdeal : Ideal (𝓞 ℚ) :=
  Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(2 : ℤ)})

lemma intTwoPrimeIdeal_isPrime : (Ideal.span {(2 : ℤ)}).IsPrime := by
  apply (Ideal.span_singleton_prime (by norm_num)).mpr
  exact Nat.prime_iff_prime_int.mp Nat.prime_two

noncomputable def rationalTwoHeightOne :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := by
  letI : (Ideal.span {(2 : ℤ)}).IsPrime := intTwoPrimeIdeal_isPrime
  have hp : rationalTwoPrimeIdeal.IsPrime :=
    Ideal.comap_isPrime Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(2 : ℤ)})
  have hp_ne : rationalTwoPrimeIdeal ≠ (⊥ : Ideal (𝓞 ℚ)) := by
    intro h
    have hspan : Ideal.span {(2 : ℤ)} = (⊥ : Ideal ℤ) :=
      Ideal.eq_bot_of_comap_eq_bot' Rat.ringOfIntegersEquiv.surjective h
    have htwo : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self _
    simp at htwo
  exact ⟨rationalTwoPrimeIdeal, hp, hp_ne⟩

noncomputable def rationalTwoPlace : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk rationalTwoHeightOne

def auditTheta (period liftedLog : ℝ) : ThetaPilotData ℚ where
  index := Fin 1
  indexFintype := inferInstance
  value := fun _ => 2
  norm := fun _ => 1
  frobenius := fun i => i
  period := fun _ => period
  liftedLog := fun _ => liftedLog

def auditPacketHull (packetWeight hullWeight : ℝ) : PacketHullData (Fin 1) where
  packet := Fin 1
  packetFintype := inferInstance
  packetToPilot := fun _ => 0
  packetWeight := fun _ => packetWeight
  hull := Fin 1
  hullFintype := inferInstance
  hullToPacket := fun _ => 0
  hullWeight := fun _ => hullWeight

noncomputable def auditData (q : ℚ) (period liftedLog logVolume packetWeight hullWeight : ℝ) :
    AdelicThetaLinkData ℚ where
  places := {rationalTwoPlace}
  qParameter := q
  theta := auditTheta period liftedLog
  packetHull := auditPacketHull packetWeight hullWeight
  qNorm := fun w => w (2 : ℚ)
  height := fun _ => 0
  logVolume := logVolume
  processionLength := 1

theorem firstAxiom_model :
    FirstAxiom (auditData 2 0 0 7 2 3) := by
  constructor
  · simp [auditData]
  · norm_num [auditData]
  · intro w hw
    change 0 < w (2 : ℚ)
    exact NumberField.FinitePlace.pos_iff.mpr (by norm_num)
  · intro x
    norm_num [auditData]
  · intro i
    change 0 < (1 : ℝ)
    norm_num
  · intro p
    change 0 < (2 : ℝ)
    norm_num
  · intro h
    change 0 < (3 : ℝ)
    norm_num

theorem firstAxiom_violation :
    ¬ FirstAxiom (auditData 0 0 0 7 2 3) := by
  intro h
  exact h.q_parameter_nonzero rfl

theorem adelicThetaLink_model :
    AdelicThetaLink (auditData 2 7 7 7 2 3) := by
  constructor
  · intro w hw j
    change w (2 : ℚ) ^ (j * j) = w ((2 : ℚ) ^ (j * j))
    exact (map_pow w (2 : ℚ) (j * j)).symm
  · intro i
    simp [auditData, auditTheta]
  · intro i
    simp [auditData, auditTheta]
  · change (7 : ℝ) = ∑ _ : Fin 1, (7 : ℝ)
    norm_num

theorem adelicThetaLink_violation :
    ¬ AdelicThetaLink (auditData 2 7 8 7 2 3) := by
  intro h
  have hp := h.period_map (0 : Fin 1)
  change (7 : ℝ) = 8 at hp
  norm_num at hp

theorem thetaLiftLog_model :
    ThetaLiftLog (auditData 2 0 0 7 2 3) := by
  constructor
  · intro i
    simp [auditData, auditTheta]
  · intro i
    change (2 : ℚ) ≠ 0
    norm_num

theorem thetaLiftLog_violation :
    ¬ ThetaLiftLog (auditData 2 0 1 7 2 3) := by
  intro h
  have hs := h.log_shell (0 : Fin 1)
  change (1 : ℝ) = Real.log 1 at hs
  norm_num at hs

theorem packetCollationHull_model :
    PacketCollationHull (auditData 2 0 0 7 2 3) := by
  constructor
  · intro p
    change (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1))
    simp
  · intro h
    change (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1))
    simp
  · intro p
    change (2 : ℝ) ≠ 0
    norm_num
  · intro h
    change (3 : ℝ) ≠ 0
    norm_num

theorem packetCollationHull_violation :
    ¬ PacketCollationHull (auditData 2 0 0 7 0 3) := by
  intro h
  have hw := h.packet_weights_nonzero (0 : Fin 1)
  change (0 : ℝ) ≠ 0 at hw
  norm_num at hw

theorem volumeTransfer_model :
    VolumeTransfer (auditData 2 0 0 5 2 3) := by
  constructor
  change (5 : ℝ) =
    (∑ _ : Fin 1, (2 : ℝ)) + ∑ _ : Fin 1, (3 : ℝ)
  norm_num

theorem volumeTransfer_violation :
    ¬ VolumeTransfer (auditData 2 0 0 6 2 3) := by
  intro h
  have hv := h.transferred_volume
  change (6 : ℝ) =
    (∑ _ : Fin 1, (2 : ℝ)) + ∑ _ : Fin 1, (3 : ℝ) at hv
  norm_num at hv

end JoshiTeich.Prologue.Audit
