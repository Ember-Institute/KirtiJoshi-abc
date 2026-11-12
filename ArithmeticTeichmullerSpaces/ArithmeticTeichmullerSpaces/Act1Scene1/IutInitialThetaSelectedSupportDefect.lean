import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedWeightedBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-SUPPORT-DEFECT
source: the actual full odd-support base q-pilot, section-selected base
places, their proved inclusion, and actual positive Tate q-orders.
fidelity: computes the omitted contribution and proves that it vanishes
exactly when the selected base support is complete. The full-support bound
retains that explicit coverage condition; no coverage or volume estimate is
assumed through a hidden field.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

def iutInitialThetaBaseQPilotLogTerm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) : ℝ :=
  Arithmetic.qPilotWeight b.1 *
    (((iutInitialThetaOddSupportBaseQPilotSource D).qOrder b : ℝ) /
      (2 * (D.prime.ℓ : ℝ))) * Real.log (Arithmetic.residueChar b.1)

theorem iutInitialThetaBaseQPilotLogTerm_pos
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    0 < iutInitialThetaBaseQPilotLogTerm D b := by
  have hq : 0 < ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder b : ℝ) := by
    exact_mod_cast (iutInitialThetaOddSupportBaseQPilotSource D).qOrder_pos b
  have hell : 0 < (D.prime.ℓ : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0 < 5) D.prime.five_le
  have hp : 1 < (Arithmetic.residueChar b.1 : ℝ) := by
    exact_mod_cast (Arithmetic.residueChar_prime b.1).one_lt
  exact mul_pos (mul_pos (Arithmetic.qPilotWeight_pos b.1)
    (div_pos hq (mul_pos (by norm_num) hell))) (Real.log_pos hp)

def iutInitialThetaFullBaseQPilotLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : ℝ :=
  ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
    iutInitialThetaBaseQPilotLogTerm D b

def iutInitialThetaOmittedBaseQPilotLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : ℝ := by
  classical
  exact ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
    if b.1 ∈ iutInitialThetaOddSupportSelectedBasePlaces D then 0
    else iutInitialThetaBaseQPilotLogTerm D b

private theorem selected_sum_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
      if b.1 ∈ iutInitialThetaOddSupportSelectedBasePlaces D then
        iutInitialThetaBaseQPilotLogTerm D b else 0) =
      iutInitialThetaSelectedWeightedQRootLogSum D := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let W := {b : NumberField.FinitePlace D.F // b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}
  let : Fintype W := (iutInitialThetaOddSupportSelectedBasePlaces_finite D).fintype
  rw [iutInitialThetaSelectedWeightedQRootLogSum_eq_baseQOrderSum D]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun b hb =>
    (⟨b.1, (Finset.mem_filter.mp hb).2⟩ : W)) ?_ ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_univ _
  · intro b hb c hc h
    exact Subtype.ext (congrArg (fun x : W => x.1) h)
  · intro w hw
    have hmem : w.1 ∈ B.badFinset := by
      apply (Set.ext_iff.mp B.badFinset_spec w.1).mpr
      exact iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D w.2
    exact ⟨⟨w.1, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.2⟩, rfl⟩
  · intro b hb
    unfold iutInitialThetaBaseQPilotLogTerm iutInitialThetaOddSupportSelectedBaseQOrder
    rfl

theorem iutInitialThetaFullBaseQPilotLogSum_eq_selected_add_omitted
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D =
      iutInitialThetaSelectedWeightedQRootLogSum D + iutInitialThetaOmittedBaseQPilotLogSum D := by
  classical
  rw [← selected_sum_eq D]
  unfold iutInitialThetaFullBaseQPilotLogSum iutInitialThetaOmittedBaseQPilotLogSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

theorem iutInitialThetaOmittedBaseQPilotLogSum_eq_zero_iff_coverage
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaOmittedBaseQPilotLogSum D = 0 ↔
      iutInitialThetaOddSupportSelectedBasePlaces D = IutOddMultiplicativeSupport D := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  constructor
  · intro hz
    apply Set.Subset.antisymm
    · exact iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport D
    · intro w hw
      have hmem : w ∈ B.badFinset := (Set.ext_iff.mp B.badFinset_spec w).mpr hw
      let b : B.badFinset := ⟨w, hmem⟩
      by_contra hnot
      have hsingle : iutInitialThetaBaseQPilotLogTerm D b ≤ iutInitialThetaOmittedBaseQPilotLogSum D := by
        unfold iutInitialThetaOmittedBaseQPilotLogSum
        have h := Finset.single_le_sum
          (f := fun c : B.badFinset => if c.1 ∈ iutInitialThetaOddSupportSelectedBasePlaces D
            then 0 else iutInitialThetaBaseQPilotLogTerm D c)
          (fun c hc => by split_ifs; exact le_rfl; exact (iutInitialThetaBaseQPilotLogTerm_pos D c).le)
          (Finset.mem_univ b)
        have hbnot : b.1 ∉ iutInitialThetaOddSupportSelectedBasePlaces D := hnot
        rw [if_neg hbnot] at h
        exact h
      have hp := iutInitialThetaBaseQPilotLogTerm_pos D b
      rw [hz] at hsingle
      linarith
  · intro hcover
    unfold iutInitialThetaOmittedBaseQPilotLogSum
    apply Finset.sum_eq_zero
    intro b hb
    have hsel : b.1 ∈ iutInitialThetaOddSupportSelectedBasePlaces D := by
      rw [hcover]
      exact B.mem_badPlaces b
    simp only [if_pos hsel]

theorem iutInitialThetaFullBaseQPilotLogSum_le_paperSum_of_coverage
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (hcover : iutInitialThetaOddSupportSelectedBasePlaces D = IutOddMultiplicativeSupport D) :
    iutInitialThetaFullBaseQPilotLogSum D ≤ iutInitialThetaSelectedQRootPaperSum D := by
  rw [iutInitialThetaFullBaseQPilotLogSum_eq_selected_add_omitted,
    (iutInitialThetaOmittedBaseQPilotLogSum_eq_zero_iff_coverage D).mpr hcover, add_zero]
  exact iutInitialThetaSelectedWeightedQRootLogSum_le_paperSum D

end
end JoshiTeich.Act1Scene1
