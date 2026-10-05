import ArithmeticTeichmullerSpaces.Act1Scene1.QNormDegreeBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceIndexBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-DEGREE-ACCOUNTING
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData.logQ`,
`QPilotData.absLogQ`) and `refer/iut/Iut/Concrete/ThetaRegion.lean`
(`QPilotInputs.qPilot`); target-side grouping:
`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`cor:cor312` (3647--3650)
fidelity: global finite-sum transport for the degree-normalized q-factor;
the raw uniformizer law and the source `(p,w)` construction remain explicit
Scene1 obligations
boundary: Scene1/Derived

The local degree adapter is useful only if its normalized factors can be
consumed by the same finite source-index bridge as the raw factors.  This file
defines that normalized grouped sum and proves the q-pilot `absLogQ` equality.
It keeps the raw target sum unchanged, so the statement-freeze review can still
choose between the two presentations without rewriting the existing proof.
-/

noncomputable def Corollary312DegreeNormalizedGroupedSourceQFactor
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (G : Corollary312SourceQGrouping p T)
    (i : G.pair) : ℝ :=
  Corollary312DegreeNormalizedSourceQFactor p T
    (show Corollary312SourceQIndex p T from
      ⟨(G.pairData i).place.1, (G.pairData i).place.2⟩)

noncomputable def Corollary312DegreeNormalizedSourceQLogSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (G : Corollary312SourceQGrouping p T) : ℝ :=
  letI := G.pairFintype
  ∑ i, -Real.log (Corollary312DegreeNormalizedGroupedSourceQFactor p T G i)

namespace Corollary312QPilotSourceIndexBridge

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {V : Corollary312VolumeData p T}
variable {P : Corollary312QPilotData p T}
variable {Q : Corollary312TateQFamily p T V}

private theorem degreeNormalizedGroupedFactor_eq_sourceFactor
    (B : Corollary312QPilotSourceIndexBridge p T V P Q)
    (w : P.badFinset) :
    Corollary312DegreeNormalizedGroupedSourceQFactor p T Q.grouping
        (B.placePairEquiv w) =
      Corollary312DegreeNormalizedSourceQFactor p T
        (show Corollary312SourceQIndex p T from
          ⟨w.1, P.mem_bad p w.2⟩) := by
  change Corollary312DegreeNormalizedSourceQFactor p T
      (show Corollary312SourceQIndex p T from
        ⟨(Q.grouping.pairData (B.placePairEquiv w)).place.1,
          (Q.grouping.pairData (B.placePairEquiv w)).place.2⟩) =
    Corollary312DegreeNormalizedSourceQFactor p T
      (show Corollary312SourceQIndex p T from
        ⟨w.1, P.mem_bad p w.2⟩)
  apply congrArg (Corollary312DegreeNormalizedSourceQFactor p T)
  apply Subtype.ext
  exact B.pair_place_eq w

theorem absLogQ_eq_degreeNormalizedSourceQLogSum
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell)
    (B : Corollary312QPilotSourceIndexBridge p T V P Q) :
    P.absLogQ p =
      Corollary312DegreeNormalizedSourceQLogSum p T Q.grouping := by
  letI := Q.grouping.pairFintype
  have hNormalize :
      P.absLogQ p =
        ∑ w ∈ P.badFinset.attach, P.normalizedLogTerm p w.1 := by
    unfold Corollary312QPilotData.absLogQ Corollary312QPilotData.logQ
    calc
      (∑ w ∈ P.badFinset.attach,
          P.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
            Real.log (Arithmetic.residueChar w.1)) /
          (2 * (T.ell : ℝ)) =
          (1 / (2 * (T.ell : ℝ))) *
            ∑ w ∈ P.badFinset.attach,
              P.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
                Real.log (Arithmetic.residueChar w.1) := by ring
      _ = ∑ w ∈ P.badFinset.attach,
          (1 / (2 * (T.ell : ℝ))) *
            (P.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
              Real.log (Arithmetic.residueChar w.1)) := by
        rw [Finset.mul_sum]
      _ = ∑ w ∈ P.badFinset.attach, P.normalizedLogTerm p w.1 := by
        rfl
  have hTerm (w : P.badFinset) :
      P.normalizedLogTerm p w.1 =
        -Real.log
          (Corollary312DegreeNormalizedGroupedSourceQFactor p T
            Q.grouping (B.placePairEquiv w)) := by
    have hLocal :=
      Corollary312QPilotData.normalizedLogTerm_eq_degreeNormalizedSourceQFactorLog
        p P hOrder hNorm hEll w.1 w.2
    rw [B.degreeNormalizedGroupedFactor_eq_sourceFactor (w := w)]
    exact hLocal
  calc
    P.absLogQ p =
        ∑ w ∈ P.badFinset.attach, P.normalizedLogTerm p w.1 := hNormalize
    _ = ∑ w : P.badFinset,
        -Real.log
          (Corollary312DegreeNormalizedGroupedSourceQFactor p T
            Q.grouping (B.placePairEquiv w)) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hTerm w
    _ = ∑ i : Q.grouping.pair,
        -Real.log
          (Corollary312DegreeNormalizedGroupedSourceQFactor p T Q.grouping i) := by
      simpa using B.placePairEquiv.sum_comp
        (fun i =>
          -Real.log
            (Corollary312DegreeNormalizedGroupedSourceQFactor p T Q.grouping i))
    _ = Corollary312DegreeNormalizedSourceQLogSum p T Q.grouping := by
      rfl

end Corollary312QPilotSourceIndexBridge

end JoshiTeich.Act1Scene1
