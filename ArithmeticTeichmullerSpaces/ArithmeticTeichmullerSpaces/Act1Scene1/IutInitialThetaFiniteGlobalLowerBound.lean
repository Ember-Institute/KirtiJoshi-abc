import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketLowerBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-GLOBAL-LOWER-BOUND
source: Joshi III `le:volume-lemma3`, `th:moccor-Mochizuki-form2`,
`cor:cor312`; reference `Cor312/LogVolume.lean`, `globalVol` and
`processionVol`, for the distinct prime sum and capsule average.
fidelity: sums the proved actual finite-packet lower bounds over primes
and averages over the standard procession. The q term is the actual VBad
q-pilot of the same InitialThetaData. Extra full-support primes contribute
zero. The exact average of j^2 is retained; no final Corollary 3.12 bound,
paper theta-locus identity, or representative-weight identity is asserted.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFiniteGlobalLowerBound

open JoshiTeich.Prologue
open IutInitialThetaFinitePacketRegion IutInitialThetaFinitePacketLogVolume
open IutInitialThetaFinitePacketLowerBound IutInitialThetaQRootFamily
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem vbadWeightedFiber_eq_zero_of_not_qPilot_char (p : ℕ)
    (hp : p ∉ (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset.image
      Arithmetic.residueChar) : vbadWeightedFiber D p = 0 := by
  rw [vbadWeightedFiber_eq_qOrderSum D p
    (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset
    (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset_spec]
  apply Finset.sum_eq_zero
  intro w hw
  exact False.elim (hp (Finset.mem_image.mpr
    ⟨w.1, w.2, (Finset.mem_filter.mp hw).2⟩))

theorem qPilot_chars_subset_badChars :
    (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset.image
      Arithmetic.residueChar ⊆ badChars D := by
  intro p hp
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
  exact bad_residueChar_mem_badChars D w
    ((IutTorsionQRootSource.iutInitialThetaQPilotData D).mem_bad hw)

theorem badChars_weighted_logSum_eq_absLogQ :
    (∑ p ∈ badChars D, Real.log p * vbadWeightedFiber D p) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  calc
    _ = ∑ p ∈ (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset.image
        Arithmetic.residueChar, Real.log p * vbadWeightedFiber D p := by
      symm
      apply Finset.sum_subset (qPilot_chars_subset_badChars D)
      intro p _ hp
      rw [vbadWeightedFiber_eq_zero_of_not_qPilot_char D p hp, mul_zero]
    _ = _ := vbadWeighted_logSum_eq_iut_absLogQ D

theorem badPrimes_weighted_logSum_eq_absLogQ :
    (∑ p ∈ badPrimes D, Real.log (p : ℕ) * vbadWeightedFiber D (p : ℕ)) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  calc
    _ = ∑ p ∈ badChars D, Real.log p * vbadWeightedFiber D p := by
      refine Finset.sum_bij (fun p _ => (p : ℕ)) ?_ ?_ ?_ ?_
      · intro p hp
        exact (mem_badPrimes D p).mp hp
      · intro p _ q _ hpq
        exact Subtype.val_injective hpq
      · intro p hp
        exact ⟨⟨p, badChars_prime D p hp⟩, (mem_badPrimes D _).mpr hp, rfl⟩
      · intro p _
        rfl
    _ = _ := badChars_weighted_logSum_eq_absLogQ D

theorem globalLogVolume_lower_bound (j : ℕ) :
    -((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ globalLogVolume D j := by
  rw [globalLogVolume_eq_sum, ← badPrimes_weighted_logSum_eq_absLogQ D, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  simpa only [mul_assoc] using packetLogVolume_lower_bound D p j

theorem globalLogVolume_bounds (j : ℕ) :
    -((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ globalLogVolume D j ∧
      globalLogVolume D j ≤ 0 :=
  ⟨globalLogVolume_lower_bound D j, globalLogVolume_nonpos D j⟩

def squareAverage : ℝ :=
  (∑ i : Index D, (((i.val + 1) ^ 2 : ℕ) : ℝ)) /
    (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ)

theorem squareAverage_pos : 0 < squareAverage D := by
  have hn := procession_length_pos D
  apply div_pos _ (by exact_mod_cast hn)
  apply Finset.sum_pos
  · intro i _
    exact_mod_cast (pow_pos (Nat.succ_pos i.val) 2)
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem processionLogVolume_lower_bound :
    -(squareAverage D * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)) ≤ processionLogVolume D := by
  have hsum :
      (∑ i : Index D, -(((i.val + 1) ^ 2 : ℕ) : ℝ) *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D)) ≤
        ∑ i : Index D, globalLogVolume D (i.val + 1) :=
    Finset.sum_le_sum fun i _ => globalLogVolume_lower_bound D (i.val + 1)
  have havg := div_le_div_of_nonneg_right hsum
    (Nat.cast_nonneg ((D.prime.ℓ - 1) / 2) : (0 : ℝ) ≤ _)
  change _ ≤ processionLogVolume D at havg
  calc
    _ = (∑ i : Index D, -(((i.val + 1) ^ 2 : ℕ) : ℝ) *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D)) /
            (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ) := by
      rw [← Finset.sum_mul, Finset.sum_neg_distrib]
      unfold squareAverage
      ring
    _ ≤ _ := havg

theorem processionLogVolume_bounds :
    -(squareAverage D * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)) ≤ processionLogVolume D ∧
      processionLogVolume D ≤ 0 :=
  ⟨processionLogVolume_lower_bound D, processionLogVolume_nonpos D⟩

theorem negative_abs_processionLogVolume_lower_bound :
    -(squareAverage D * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)) ≤ -|processionLogVolume D| := by
  rw [negative_abs_processionLogVolume]
  exact processionLogVolume_lower_bound D

end
end JoshiTeich.Act1Scene1.IutInitialThetaFiniteGlobalLowerBound
