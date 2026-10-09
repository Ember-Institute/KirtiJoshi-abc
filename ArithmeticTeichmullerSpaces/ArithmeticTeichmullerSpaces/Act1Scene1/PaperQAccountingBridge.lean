import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQNormalizationBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceIndexBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-PAPER-NORMALIZED-INDEX
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData.absLogQ`);
target grouping: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`cor:cor312` (3647--3650)
fidelity: transports the already proved weighted paper-normalized q-pilot sum
through the explicit finite source-index equivalence; the paper carrier and
unweighted sum remain construction obligations
boundary: Scene1/Derived

The paper-normalized local factor lives on the source `(p,w)` index while the
q-pilot lives on its bad-place subtype.  This file records the finite-index
transport without choosing the final raw versus normalized target statement.
-/

noncomputable def Corollary312PaperNormalizedGroupedSourceQFactor
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (G : Corollary312SourceQGrouping p T)
    (i : G.pair) : ℝ :=
  Corollary312PaperNormalizedSourceQFactor p T
    (show Corollary312SourceQIndex p T from
      ⟨(G.pairData i).place.1, (G.pairData i).place.2⟩)

noncomputable def Corollary312WeightedPaperNormalizedSourceQLogSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (G : Corollary312SourceQGrouping p T) : ℝ :=
  letI := G.pairFintype
  ∑ i,
    Arithmetic.qPilotWeight (G.pairData i).place.1 *
      -Real.log (Corollary312PaperNormalizedGroupedSourceQFactor p T G i)

namespace Corollary312QPilotSourceIndexBridge

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {V : Corollary312VolumeData p T}
variable {P : Corollary312QPilotData p T}
variable {Q : Corollary312TateQFamily p T V}

private theorem paperNormalizedGroupedFactor_eq_sourceFactor
    (B : Corollary312QPilotSourceIndexBridge p T V P Q)
    (w : P.badFinset) :
    Corollary312PaperNormalizedGroupedSourceQFactor p T Q.grouping
        (B.placePairEquiv w) =
      Corollary312PaperNormalizedSourceQFactor p T
        (show Corollary312SourceQIndex p T from
          ⟨w.1, P.mem_bad p w.2⟩) := by
  change Corollary312PaperNormalizedSourceQFactor p T
      (show Corollary312SourceQIndex p T from
        ⟨(Q.grouping.pairData (B.placePairEquiv w)).place.1,
          (Q.grouping.pairData (B.placePairEquiv w)).place.2⟩) =
    Corollary312PaperNormalizedSourceQFactor p T
      (show Corollary312SourceQIndex p T from
        ⟨w.1, P.mem_bad p w.2⟩)
  apply congrArg (Corollary312PaperNormalizedSourceQFactor p T)
  apply Subtype.ext
  exact B.pair_place_eq w

theorem absLogQ_eq_weightedPaperNormalizedSourceQLogSum
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell)
    (B : Corollary312QPilotSourceIndexBridge p T V P Q) :
    P.absLogQ p =
      Corollary312WeightedPaperNormalizedSourceQLogSum p T Q.grouping := by
  letI := Q.grouping.pairFintype
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
          -Real.log
            (Corollary312PaperNormalizedGroupedSourceQFactor p T Q.grouping
              (B.placePairEquiv w)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [paperNormalizedGroupedFactor_eq_sourceFactor (p := p) B w]
    _ = ∑ w : P.badFinset,
        Arithmetic.qPilotWeight (Q.grouping.pairData (B.placePairEquiv w)).place.1 *
          -Real.log
            (Corollary312PaperNormalizedGroupedSourceQFactor p T Q.grouping
              (B.placePairEquiv w)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [B.pair_place_eq w]
    _ = ∑ i : Q.grouping.pair,
        Arithmetic.qPilotWeight (Q.grouping.pairData i).place.1 *
          -Real.log
            (Corollary312PaperNormalizedGroupedSourceQFactor p T Q.grouping i) := by
      simpa using B.placePairEquiv.sum_comp
        (fun i =>
          Arithmetic.qPilotWeight (Q.grouping.pairData i).place.1 *
            -Real.log
              (Corollary312PaperNormalizedGroupedSourceQFactor p T Q.grouping i))
    _ = Corollary312WeightedPaperNormalizedSourceQLogSum p T Q.grouping := by
      rfl

end Corollary312QPilotSourceIndexBridge

end JoshiTeich.Act1Scene1
