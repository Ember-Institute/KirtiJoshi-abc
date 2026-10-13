import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQNormalizationBridge

/-!
source-id: JT-SCENE1-PAPER-REPRESENTATIVE-FIBER-MASS
source: the actual finite q-pilot arithmetic weights, their rational-prime
bound, and the proved weighted paper-normalized q-log identity.
fidelity: computes representative fibre masses from the source and proves
weighted regrouping and a conditional unweighted upper bound. It does not
assume mass one, construct the paper representative map, or identify this
upper bound with the frozen Corollary 3.12 target.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u

noncomputable section
variable {K : Type u} [Field K] [NumberField K]
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {R : Type u} [DecidableEq R]

def qPilotRepresentativeFiberMass (P : Corollary312QPilotData p T)
    (f : P.badFinset → R) (r : R) : ℝ :=
  ∑ w : P.badFinset, if f w = r then Arithmetic.qPilotWeight w.1 else 0

theorem qPilotWeightedSourceSum_eq_fiberMassSum [Fintype R]
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (term : R → ℝ) :
    (∑ w : P.badFinset, Arithmetic.qPilotWeight w.1 * term (f w)) =
      ∑ r, qPilotRepresentativeFiberMass p P f r * term r := by
  calc
    (∑ w : P.badFinset, Arithmetic.qPilotWeight w.1 * term (f w)) =
        ∑ w : P.badFinset, ∑ r : R,
          if f w = r then Arithmetic.qPilotWeight w.1 * term r else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      simp
    _ = ∑ r : R, ∑ w : P.badFinset,
        if f w = r then Arithmetic.qPilotWeight w.1 * term r else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r, qPilotRepresentativeFiberMass p P f r * term r := by
      unfold qPilotRepresentativeFiberMass
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : f w = r <;> simp [h]

private theorem sourcePrimeMass_le_one
    (P : Corollary312QPilotData p T) (q : ℕ) (hq : q.Prime) :
    (∑ w : P.badFinset,
      if Arithmetic.residueChar w.1 = q then Arithmetic.qPilotWeight w.1 else 0) ≤ 1 := by
  classical
  have h := Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter P.badFinset q hq
  rw [Finset.sum_filter] at h
  have hsum :
      (∑ w : P.badFinset,
        if Arithmetic.residueChar w.1 = q then Arithmetic.qPilotWeight w.1 else 0) =
      ∑ w ∈ P.badFinset,
        if Arithmetic.residueChar w = q then Arithmetic.qPilotWeight w else 0 := by
    refine Finset.sum_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
    · intro w hw
      exact w.2
    · intro w hw v hv h
      exact Subtype.ext h
    · intro w hw
      exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
    · intro w hw
      rfl
  rw [hsum]
  exact h

theorem qPilotRepresentativeFiberMass_mem_unitInterval
    (P : Corollary312QPilotData p T) (f : P.badFinset → R)
    (primeLabel : R → ℕ)
    (hPrime : ∀ w : P.badFinset, Arithmetic.residueChar w.1 = primeLabel (f w))
    (r : R) :
    0 ≤ qPilotRepresentativeFiberMass p P f r ∧
      qPilotRepresentativeFiberMass p P f r ≤ 1 := by
  classical
  constructor
  · unfold qPilotRepresentativeFiberMass
    apply Finset.sum_nonneg
    intro w hw
    split_ifs
    · exact (Arithmetic.qPilotWeight_pos w.1).le
    · exact le_rfl
  · by_cases hf : ∃ w, f w = r
    · obtain ⟨w₀, hw₀⟩ := hf
      have hq : (primeLabel r).Prime := by
        rw [← hw₀, ← hPrime w₀]
        exact Arithmetic.residueChar_prime w₀.1
      have hlocal (w : P.badFinset) :
          (if f w = r then Arithmetic.qPilotWeight w.1 else 0) ≤
          (if Arithmetic.residueChar w.1 = primeLabel r then
            Arithmetic.qPilotWeight w.1 else 0) := by
        by_cases hr : f w = r
        · have hp : Arithmetic.residueChar w.1 = primeLabel r := by
            rw [hPrime w, hr]
          simp only [ite_eq_left hr, ite_eq_left hp, le_refl]
        · simp only [ite_eq_right hr]
          split_ifs
          · exact (Arithmetic.qPilotWeight_pos w.1).le
          · exact le_rfl
      exact le_trans (Finset.sum_le_sum (fun w hw => hlocal w))
        (sourcePrimeMass_le_one p P (primeLabel r) hq)
    · have hne : ∀ w, f w ≠ r := by
        intro w hw
        exact hf ⟨w, hw⟩
      simp [qPilotRepresentativeFiberMass, hne]

namespace Corollary312QPilotData

theorem absLogQ_eq_fiberMassRepresentativeSum [Fintype R]
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (term : R → ℝ)
    (hTerm : ∀ w : P.badFinset,
      -Real.log (Corollary312PaperNormalizedSourceQFactor p T
        ⟨w.1, P.mem_bad p w.2⟩) = term (f w))
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    P.absLogQ p = ∑ r, qPilotRepresentativeFiberMass p P f r * term r := by
  calc
    P.absLogQ p = ∑ w : P.badFinset,
        Arithmetic.qPilotWeight w.1 *
          -Real.log (Corollary312PaperNormalizedSourceQFactor p T
            ⟨w.1, P.mem_bad p w.2⟩) :=
      absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum p T P hOrder hRaw hEll
    _ = ∑ w : P.badFinset, Arithmetic.qPilotWeight w.1 * term (f w) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hTerm w]
    _ = ∑ r, qPilotRepresentativeFiberMass p P f r * term r :=
      qPilotWeightedSourceSum_eq_fiberMassSum p P f term

theorem absLogQ_le_unweightedRepresentativeSum [Fintype R]
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (term : R → ℝ)
    (hTerm : ∀ w : P.badFinset,
      -Real.log (Corollary312PaperNormalizedSourceQFactor p T
        ⟨w.1, P.mem_bad p w.2⟩) = term (f w))
    (primeLabel : R → ℕ)
    (hPrime : ∀ w : P.badFinset, Arithmetic.residueChar w.1 = primeLabel (f w))
    (hNonneg : ∀ r, 0 ≤ term r)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    P.absLogQ p ≤ ∑ r, term r := by
  rw [P.absLogQ_eq_fiberMassRepresentativeSum p f term hTerm hOrder hRaw hEll]
  apply Finset.sum_le_sum
  intro r hr
  have hmass := qPilotRepresentativeFiberMass_mem_unitInterval p P f primeLabel hPrime r
  calc
    qPilotRepresentativeFiberMass p P f r * term r ≤ 1 * term r :=
      mul_le_mul_of_nonneg_right hmass.2 (hNonneg r)
    _ = term r := one_mul _

end Corollary312QPilotData
end
end JoshiTeich.Act1Scene1
