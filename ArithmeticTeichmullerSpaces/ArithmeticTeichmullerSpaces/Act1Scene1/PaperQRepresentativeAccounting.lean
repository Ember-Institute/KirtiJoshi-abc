import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQAccountingBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

noncomputable section

/-!
source-id: IUT-COR312-PAPER-REPRESENTATIVE-MULTIPLICITY
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData.absLogQ`)
and `refer/iut/Iut/Concrete/ThetaRegion.lean` (`QPilotInputs.qPilot`);
target-side representative carrier: `JoshiTeich: refer/JoshiTeich/index-Arithmetic
Teichmuller Spaces 3.md`, `cor:cor312` (3647--3650).
fidelity: isolates the exact finite representative-multiplicity certificate
needed to turn the degree-weighted q-pilot sum into an unweighted paper sum;
the certificate itself must still be supplied by the paper representative
construction.
boundary: Scene1/Derived

The q-pilot carrier and the paper representative carrier need not have the
same cardinality.  The fields below make that difference explicit: each q-pilot
place is sent to a paper representative, its local paper term is identified,
and the total q-pilot weight in every representative fiber is required to be
one.  The final equality is then a finite-sum theorem, rather than a hidden
identification of the two carriers.
-/

structure Corollary312QPilotPaperRepresentativeAccounting
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (P : Corollary312QPilotData p T) where
  /-- The finite carrier of the paper's selected representatives. -/
  representative : Type uK
  representativeFintype : Fintype representative
  [representativeDecidableEq : DecidableEq representative]
  /-- The paper-normalized logarithmic term at each representative. -/
  representativeTerm : representative → ℝ
  /-- Source-to-paper representative map. -/
  representativeOfSource : P.badFinset → representative
  /-- The source local paper factor is the term of its representative. -/
  sourceTerm_eq : ∀ w : P.badFinset,
    -Real.log
        (Corollary312PaperNormalizedSourceQFactor p T
          (show Corollary312SourceQIndex p T from
            ⟨w.1, P.mem_bad p w.2⟩)) =
      representativeTerm (representativeOfSource w)
  /-- The q-pilot weight has total mass one in every representative fiber. -/
  weight_fiber_sum_eq_one : ∀ r : representative,
    (∑ w : P.badFinset,
      if representativeOfSource w = r then
        Arithmetic.qPilotWeight w.1
      else 0) = 1

namespace Corollary312QPilotPaperRepresentativeAccounting

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {P : Corollary312QPilotData p T}

noncomputable def representativePaperNormalizedSourceQFactorProduct
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative] : ℝ :=
  ∏ r : A.representative, Real.exp (-A.representativeTerm r)

private theorem weighted_source_sum_eq_representative_sum
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative] :
    (∑ w : P.badFinset,
      Arithmetic.qPilotWeight w.1 *
        A.representativeTerm (A.representativeOfSource w)) =
      ∑ r : A.representative, A.representativeTerm r := by
  let _ := A.representativeDecidableEq
  calc
    (∑ w : P.badFinset,
        Arithmetic.qPilotWeight w.1 *
          A.representativeTerm (A.representativeOfSource w)) =
        ∑ w : P.badFinset, ∑ r : A.representative,
          if A.representativeOfSource w = r then
            Arithmetic.qPilotWeight w.1 * A.representativeTerm r
          else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      simp
    _ = ∑ r : A.representative, ∑ w : P.badFinset,
          if A.representativeOfSource w = r then
            Arithmetic.qPilotWeight w.1 * A.representativeTerm r
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r : A.representative,
          A.representativeTerm r *
            ∑ w : P.badFinset,
              if A.representativeOfSource w = r then
                Arithmetic.qPilotWeight w.1
              else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h : A.representativeOfSource w = r
      · simp [h]
        ring
      · simp [h]
    _ = ∑ r : A.representative, A.representativeTerm r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [A.weight_fiber_sum_eq_one r]
      ring

/-- A representative-multiplicity certificate turns the q-pilot sum into the
paper's unweighted representative sum.  Constructing the certificate from the
actual `L'` representatives remains a separate source obligation. -/
theorem absLogQ_eq_unweightedRepresentativeSum
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative]
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    P.absLogQ p =
      ∑ r : A.representative, A.representativeTerm r := by
  let _ := A.representativeDecidableEq
  have hWeighted :=
    absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum
      (p := p) T P hOrder hNorm hEll
  calc
    P.absLogQ p =
        ∑ w : P.badFinset,
          Arithmetic.qPilotWeight w.1 *
            -Real.log
              (Corollary312PaperNormalizedSourceQFactor p T
                (show Corollary312SourceQIndex p T from
                  ⟨w.1, P.mem_bad p w.2⟩)) := hWeighted
    _ = ∑ w : P.badFinset,
          Arithmetic.qPilotWeight w.1 *
            A.representativeTerm (A.representativeOfSource w) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [A.sourceTerm_eq w]
    _ = ∑ r : A.representative, A.representativeTerm r :=
      weighted_source_sum_eq_representative_sum p A

theorem weightedPaperNormalizedSourceQFactorProduct_eq_representativePaperNormalizedSourceQFactorProduct
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    [Fintype A.representative]
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    weightedPaperNormalizedSourceQFactorProduct p T P =
      representativePaperNormalizedSourceQFactorProduct p A := by
  let _ := A.representativeDecidableEq
  have hProduct := weightedPaperNormalizedSourceQFactorProduct_eq_exp_neg_absLogQ
    p T P hOrder hNorm hEll
  have hSum := absLogQ_eq_unweightedRepresentativeSum p A hOrder hNorm hEll
  calc
    weightedPaperNormalizedSourceQFactorProduct p T P =
        Real.exp (-P.absLogQ p) := hProduct
    _ = Real.exp (-∑ r : A.representative, A.representativeTerm r) := by
      rw [hSum]
    _ = representativePaperNormalizedSourceQFactorProduct p A := by
      unfold representativePaperNormalizedSourceQFactorProduct
      rw [← Finset.sum_neg_distrib, Real.exp_sum]

end Corollary312QPilotPaperRepresentativeAccounting

end

end JoshiTeich.Act1Scene1
