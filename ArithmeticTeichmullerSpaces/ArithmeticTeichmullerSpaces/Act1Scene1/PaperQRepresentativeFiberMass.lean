import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQNormalizationBridge
import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.BaseChange

/-!
source-id: JT-SCENE1-PAPER-REPRESENTATIVE-FIBER-MASS
source: the actual finite q-pilot arithmetic weights, their rational-prime
bound, and the proved weighted paper-normalized q-log identity.
fidelity: computes representative fibre masses from the source and proves
weighted regrouping, the exact unweighted deficit, and a mass-one equality
criterion when all representative terms are positive. It does not
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

theorem qPilotWeight_sum_lt_one_of_ramified_of_residueChar
    (S : Finset (NumberField.FinitePlace K)) (q : ℕ) (hq : q.Prime)
    (hS : ∀ w ∈ S, Arithmetic.residueChar w = q)
    (w : NumberField.FinitePlace K) (hw : w ∈ S)
    (hRam : 1 < Arithmetic.ramIdx w) :
    ∑ v ∈ S, Arithmetic.qPilotWeight v < 1 := by
  have hfilter : S.filter (fun v => Arithmetic.residueChar v = q) = S :=
    Finset.filter_eq_self.mpr hS
  have hdegree := Arithmetic.localDeg_sum_le_finrank_of_residueChar_filter S q hq
  rw [hfilter] at hdegree
  have hpoint (v : NumberField.FinitePlace K) (_ : v ∈ S) :
      Arithmetic.inertDeg v ≤ Arithmetic.localDeg v := by
    unfold Arithmetic.localDeg
    exact Nat.le_mul_of_pos_left _ (Arithmetic.ramIdx_pos v)
  have hstrict : Arithmetic.inertDeg w < Arithmetic.localDeg w := by
    unfold Arithmetic.localDeg
    nlinarith [Arithmetic.inertDeg_pos w]
  have hsum := (Finset.sum_lt_sum hpoint ⟨w, hw, hstrict⟩).trans_le hdegree
  unfold Arithmetic.qPilotWeight
  rw [← Finset.sum_div]
  apply (div_lt_one Arithmetic.finrank_pos).mpr
  exact_mod_cast hsum

/-- Mass one requires both saturation of the local-degree bound and
ramification index one at every place in the finite source. -/
theorem qPilotWeight_sum_eq_one_iff_degree_sum_eq_and_unramified
    (S : Finset (NumberField.FinitePlace K)) (q : ℕ) (hq : q.Prime)
    (hS : ∀ w ∈ S, Arithmetic.residueChar w = q) :
    (∑ w ∈ S, Arithmetic.qPilotWeight w) = 1 ↔
      (∑ w ∈ S, Arithmetic.localDeg w) = Module.finrank ℚ K ∧
        ∀ w ∈ S, Arithmetic.ramIdx w = 1 := by
  have hdegreeNe : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    Arithmetic.finrank_pos.ne'
  constructor
  · intro hmass
    have hunram (w : NumberField.FinitePlace K) (hw : w ∈ S) :
        Arithmetic.ramIdx w = 1 := by
      by_contra hne
      have hRam : 1 < Arithmetic.ramIdx w := by
        have := Arithmetic.ramIdx_pos w
        omega
      have hlt := qPilotWeight_sum_lt_one_of_ramified_of_residueChar S q hq hS w hw hRam
      rw [hmass] at hlt
      exact (lt_irrefl 1) hlt
    refine ⟨?_, hunram⟩
    have hinert : (∑ w ∈ S, (Arithmetic.inertDeg w : ℝ)) =
        (Module.finrank ℚ K : ℝ) := by
      unfold Arithmetic.qPilotWeight at hmass
      rw [← Finset.sum_div] at hmass
      exact (div_eq_one_iff_eq hdegreeNe).mp hmass
    have heq : (∑ w ∈ S, Arithmetic.localDeg w) = ∑ w ∈ S, Arithmetic.inertDeg w :=
      Finset.sum_congr rfl fun w hw => by simp [Arithmetic.localDeg, hunram w hw]
    rw [heq]
    exact_mod_cast hinert
  · rintro ⟨hdegree, hunram⟩
    have hinert : (∑ w ∈ S, Arithmetic.inertDeg w) = Module.finrank ℚ K := by
      rw [← hdegree]
      exact Finset.sum_congr rfl fun w hw => by
        simp [Arithmetic.localDeg, hunram w hw]
    unfold Arithmetic.qPilotWeight
    rw [← Finset.sum_div, ← Nat.cast_sum, hinert, div_self hdegreeNe]

/-- Saturating the degree bound means covering every actual place above the
prime. Omitting even one place leaves a positive local degree unaccounted for. -/
theorem localDeg_sum_eq_finrank_iff_full_prime_fiber
    (S : Finset (NumberField.FinitePlace K)) (q : ℕ) (hq : q.Prime)
    (hS : ∀ w ∈ S, Arithmetic.residueChar w = q) :
    (∑ w ∈ S, Arithmetic.localDeg w) = Module.finrank ℚ K ↔
      ∀ w : NumberField.FinitePlace K, Arithmetic.residueChar w = q → w ∈ S := by
  classical
  constructor
  · intro hdegree w hw
    by_contra hnot
    have hfilter : (insert w S).filter (fun v => Arithmetic.residueChar v = q) =
        insert w S := by
      apply Finset.filter_eq_self.mpr
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hw
      · exact hS v hv
    have hbound := Arithmetic.localDeg_sum_le_finrank_of_residueChar_filter
      (insert w S) q hq
    rw [hfilter, Finset.sum_insert hnot, hdegree] at hbound
    have hpos := Arithmetic.localDeg_pos w
    omega
  · intro hcover
    let : Finite {w : NumberField.FinitePlace K // Arithmetic.residueChar w = q} :=
      Arithmetic.fiber_finite q
    let : Fintype {w : NumberField.FinitePlace K // Arithmetic.residueChar w = q} :=
      Fintype.ofFinite _
    rw [← Arithmetic.sum_localDeg (K := K) q hq]
    symm
    refine Finset.sum_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
    · intro w _
      exact hcover w.1 w.2
    · intro w _ v _ h
      exact Subtype.ext h
    · intro w hw
      exact ⟨⟨w, hS w hw⟩, Finset.mem_univ _, rfl⟩
    · intro w _
      rfl

theorem qPilotWeight_sum_eq_one_iff_full_prime_fiber_and_unramified
    (S : Finset (NumberField.FinitePlace K)) (q : ℕ) (hq : q.Prime)
    (hS : ∀ w ∈ S, Arithmetic.residueChar w = q) :
    (∑ w ∈ S, Arithmetic.qPilotWeight w) = 1 ↔
      (∀ w : NumberField.FinitePlace K, Arithmetic.residueChar w = q → w ∈ S) ∧
        ∀ w ∈ S, Arithmetic.ramIdx w = 1 := by
  rw [qPilotWeight_sum_eq_one_iff_degree_sum_eq_and_unramified S q hq hS,
    localDeg_sum_eq_finrank_iff_full_prime_fiber S q hq hS]

/-- The finite-place support of one representative fibre, without a paper
identity or a mass-one assumption. -/
def qPilotRepresentativeFiberFinset (P : Corollary312QPilotData p T)
    (f : P.badFinset → R) (r : R) : Finset (NumberField.FinitePlace K) := by
  classical
  exact (Finset.univ.filter (fun w : P.badFinset => f w = r)).image Subtype.val

theorem mem_qPilotRepresentativeFiberFinset_iff
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (r : R)
    (w : NumberField.FinitePlace K) :
    w ∈ qPilotRepresentativeFiberFinset p P f r ↔
      ∃ hw : w ∈ P.badFinset, f ⟨w, hw⟩ = r := by
  classical
  simp only [qPilotRepresentativeFiberFinset, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hw, hf⟩
    exact ⟨⟨w, hw⟩, hf, rfl⟩

theorem qPilotRepresentativeFiberMass_eq_fiberFinset_sum
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (r : R) :
    qPilotRepresentativeFiberMass p P f r =
      ∑ w ∈ qPilotRepresentativeFiberFinset p P f r, Arithmetic.qPilotWeight w := by
  classical
  rw [qPilotRepresentativeFiberFinset, Finset.sum_image]
  · rw [Finset.sum_filter]
    rfl
  · intro w _ v _ h
    exact Subtype.ext h

/-- For a prime-preserving representative map, mass one is equivalent to
the fibre containing all places above its prime, each with ramification index
one. This concerns the actual source; it does not construct paper representatives. -/
theorem qPilotRepresentativeFiberMass_eq_one_iff_full_prime_fiber_and_unramified
    (P : Corollary312QPilotData p T) (f : P.badFinset → R)
    (primeLabel : R → ℕ)
    (hPrime : ∀ w : P.badFinset, Arithmetic.residueChar w.1 = primeLabel (f w))
    (r : R) (hq : (primeLabel r).Prime) :
    qPilotRepresentativeFiberMass p P f r = 1 ↔
      (∀ w : NumberField.FinitePlace K, Arithmetic.residueChar w = primeLabel r →
        ∃ hw : w ∈ P.badFinset, f ⟨w, hw⟩ = r) ∧
      ∀ w : P.badFinset, f w = r → Arithmetic.ramIdx w.1 = 1 := by
  have hS (w : NumberField.FinitePlace K)
      (hw : w ∈ qPilotRepresentativeFiberFinset p P f r) :
      Arithmetic.residueChar w = primeLabel r := by
    obtain ⟨hw, hf⟩ := (mem_qPilotRepresentativeFiberFinset_iff p P f r w).mp hw
    exact (hPrime ⟨w, hw⟩).trans (congrArg primeLabel hf)
  rw [qPilotRepresentativeFiberMass_eq_fiberFinset_sum p P f r,
    qPilotWeight_sum_eq_one_iff_full_prime_fiber_and_unramified
      (qPilotRepresentativeFiberFinset p P f r) (primeLabel r) hq hS]
  simp only [mem_qPilotRepresentativeFiberFinset_iff]
  constructor
  · rintro ⟨hcover, hunram⟩
    exact ⟨hcover, fun w hw => hunram w.1 ⟨w.2, hw⟩⟩
  · rintro ⟨hcover, hunram⟩
    refine ⟨hcover, ?_⟩
    rintro w ⟨hw, hf⟩
    exact hunram ⟨w, hw⟩ hf

private theorem sourcePrimeMass_eq_filter_sum
    (P : Corollary312QPilotData p T) (q : ℕ) :
    (∑ w : P.badFinset,
      if Arithmetic.residueChar w.1 = q then Arithmetic.qPilotWeight w.1 else 0) =
      ∑ w ∈ P.badFinset.filter (fun w => Arithmetic.residueChar w = q),
        Arithmetic.qPilotWeight w := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
  · intro w hw
    exact w.2
  · intro w hw v hv h
    exact Subtype.ext h
  · intro w hw
    exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
  · intro w hw
    rfl

private theorem sourcePrimeMass_le_one
    (P : Corollary312QPilotData p T) (q : ℕ) (hq : q.Prime) :
    (∑ w : P.badFinset,
      if Arithmetic.residueChar w.1 = q then Arithmetic.qPilotWeight w.1 else 0) ≤ 1 := by
  rw [sourcePrimeMass_eq_filter_sum p P q]
  exact Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter P.badFinset q hq

private theorem fiberMass_le_sourcePrimeMass
    (P : Corollary312QPilotData p T) (f : P.badFinset → R)
    (primeLabel : R → ℕ)
    (hPrime : ∀ w : P.badFinset, Arithmetic.residueChar w.1 = primeLabel (f w))
    (r : R) :
    qPilotRepresentativeFiberMass p P f r ≤
      ∑ w : P.badFinset,
        if Arithmetic.residueChar w.1 = primeLabel r then Arithmetic.qPilotWeight w.1 else 0 := by
  unfold qPilotRepresentativeFiberMass
  apply Finset.sum_le_sum
  intro w hw
  by_cases hr : f w = r
  · have hp : Arithmetic.residueChar w.1 = primeLabel r := by rw [hPrime w, hr]
    simp only [if_pos hr, if_pos hp, le_refl]
  · simp only [if_neg hr]
    split_ifs
    · exact (Arithmetic.qPilotWeight_pos w.1).le
    · exact le_rfl

theorem qPilotRepresentativeFiberMass_lt_one_of_ramified_source
    (P : Corollary312QPilotData p T) (f : P.badFinset → R)
    (primeLabel : R → ℕ)
    (hPrime : ∀ w : P.badFinset, Arithmetic.residueChar w.1 = primeLabel (f w))
    (w : P.badFinset) (hRam : 1 < Arithmetic.ramIdx w.1) :
    qPilotRepresentativeFiberMass p P f (f w) < 1 := by
  classical
  have hq : (primeLabel (f w)).Prime := by
    rw [← hPrime w]
    exact Arithmetic.residueChar_prime w.1
  have hstrict : (∑ v : P.badFinset,
      if Arithmetic.residueChar v.1 = primeLabel (f w) then
        Arithmetic.qPilotWeight v.1 else 0) < 1 := by
    rw [sourcePrimeMass_eq_filter_sum p P (primeLabel (f w))]
    exact qPilotWeight_sum_lt_one_of_ramified_of_residueChar
      (P.badFinset.filter (fun v => Arithmetic.residueChar v = primeLabel (f w)))
      (primeLabel (f w)) hq (fun v hv => (Finset.mem_filter.mp hv).2)
      w.1 (Finset.mem_filter.mpr ⟨w.2, hPrime w⟩) hRam
  exact (fiberMass_le_sourcePrimeMass p P f primeLabel hPrime (f w)).trans_lt hstrict

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
      exact le_trans (fiberMass_le_sourcePrimeMass p P f primeLabel hPrime r)
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

/-- The unweighted excess is exactly the sum of the missing fibre masses
times their representative terms. No mass-one certificate is assumed. -/
theorem unweightedRepresentativeSum_sub_absLogQ_eq_fiberMassDefectSum [Fintype R]
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (term : R → ℝ)
    (hTerm : ∀ w : P.badFinset,
      -Real.log (Corollary312PaperNormalizedSourceQFactor p T
        ⟨w.1, P.mem_bad p w.2⟩) = term (f w))
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    (∑ r, term r) - P.absLogQ p =
      ∑ r, (1 - qPilotRepresentativeFiberMass p P f r) * term r := by
  rw [P.absLogQ_eq_fiberMassRepresentativeSum p f term hTerm hOrder hRaw hEll,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- For positive terms and a prime-preserving map, equality with the
unweighted sum requires mass one in every representative fibre. -/
theorem absLogQ_eq_unweightedRepresentativeSum_iff_fiberMass_eq_one [Fintype R]
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (term : R → ℝ)
    (hTerm : ∀ w : P.badFinset,
      -Real.log (Corollary312PaperNormalizedSourceQFactor p T
        ⟨w.1, P.mem_bad p w.2⟩) = term (f w))
    (primeLabel : R → ℕ)
    (hPrime : ∀ w : P.badFinset, Arithmetic.residueChar w.1 = primeLabel (f w))
    (hPos : ∀ r, 0 < term r)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    P.absLogQ p = ∑ r, term r ↔
      ∀ r, qPilotRepresentativeFiberMass p P f r = 1 := by
  have hnonneg (r : R) :
      0 ≤ (1 - qPilotRepresentativeFiberMass p P f r) * term r :=
    mul_nonneg (sub_nonneg.mpr
      (qPilotRepresentativeFiberMass_mem_unitInterval p P f primeLabel hPrime r).2)
      (hPos r).le
  constructor
  · intro heq r
    have hsum : (∑ s, (1 - qPilotRepresentativeFiberMass p P f s) * term s) = 0 := by
      rw [← P.unweightedRepresentativeSum_sub_absLogQ_eq_fiberMassDefectSum
        p f term hTerm hOrder hRaw hEll, heq, sub_self]
    have hsingle := Finset.single_le_sum
      (f := fun s : R => (1 - qPilotRepresentativeFiberMass p P f s) * term s)
      (fun s _ => hnonneg s) (Finset.mem_univ r)
    have hzero : (1 - qPilotRepresentativeFiberMass p P f r) * term r = 0 := by
      rw [hsum] at hsingle
      exact le_antisymm hsingle (hnonneg r)
    have hmass : 1 - qPilotRepresentativeFiberMass p P f r = 0 :=
      (mul_eq_zero.mp hzero).resolve_right (hPos r).ne'
    linarith
  · intro hmass
    rw [P.absLogQ_eq_fiberMassRepresentativeSum p f term hTerm hOrder hRaw hEll]
    simp_rw [hmass, one_mul]

theorem absLogQ_lt_unweightedRepresentativeSum_iff_exists_fiberMass_lt_one [Fintype R]
    (P : Corollary312QPilotData p T) (f : P.badFinset → R) (term : R → ℝ)
    (hTerm : ∀ w : P.badFinset,
      -Real.log (Corollary312PaperNormalizedSourceQFactor p T
        ⟨w.1, P.mem_bad p w.2⟩) = term (f w))
    (primeLabel : R → ℕ)
    (hPrime : ∀ w : P.badFinset, Arithmetic.residueChar w.1 = primeLabel (f w))
    (hPos : ∀ r, 0 < term r)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    P.absLogQ p < ∑ r, term r ↔
      ∃ r, qPilotRepresentativeFiberMass p P f r < 1 := by
  have heq := P.absLogQ_eq_unweightedRepresentativeSum_iff_fiberMass_eq_one
    p f term hTerm primeLabel hPrime hPos hOrder hRaw hEll
  constructor
  · intro hlt
    by_contra hnone
    have hmass : ∀ r, qPilotRepresentativeFiberMass p P f r = 1 := by
      intro r
      have hle :=
        (qPilotRepresentativeFiberMass_mem_unitInterval p P f primeLabel hPrime r).2
      have hge : 1 ≤ qPilotRepresentativeFiberMass p P f r :=
        not_lt.mp (fun hr => hnone ⟨r, hr⟩)
      exact le_antisymm hle hge
    exact (ne_of_lt hlt) (heq.mpr hmass)
  · rintro ⟨r, hr⟩
    have hle := P.absLogQ_le_unweightedRepresentativeSum
      p f term hTerm primeLabel hPrime (fun s => (hPos s).le) hOrder hRaw hEll
    have hne : P.absLogQ p ≠ ∑ s, term s := by
      intro h
      exact (ne_of_lt hr) (heq.mp h r)
    exact lt_of_le_of_ne hle hne

end Corollary312QPilotData
end
end JoshiTeich.Act1Scene1
