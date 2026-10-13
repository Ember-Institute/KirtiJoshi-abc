import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotDegreeAccountingBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.RawTargetSpecification

/-!
source-id: JT-SCENE1-QPILOT-RAW-DEGREE-ACCOUNTING
source: the proved local degree adapter and finite source-index transport;
Joshi III `cor:cor312` and the local normalization in `th:moccor` distinguish
the paper absolute value from the current raw completion-norm candidate.
fidelity: evaluates the global degree coefficient between the current raw
grouped q-sum and the q-pilot. It preserves the raw candidate and does not
identify it with the paper-normalized unweighted representative sum.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem degreeNormalizedSourceQLogSum_eq_raw_div_degree
    (T : Corollary312Data K O p) (G : Corollary312SourceQGrouping p T) :
    Corollary312DegreeNormalizedSourceQLogSum p T G =
      Corollary312RawSourceQLogSum p T G / (Module.finrank ℚ K : ℝ) := by
  let := G.pairFintype
  unfold Corollary312DegreeNormalizedSourceQLogSum Corollary312RawSourceQLogSum
  calc
    (∑ i, -Real.log (Corollary312DegreeNormalizedGroupedSourceQFactor p T G i)) =
        ∑ i, (1 / (Module.finrank ℚ K : ℝ)) *
          (-Real.log (Corollary312GroupedSourceQFactor p T G i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact degreeNormalizedSourceQFactor_log_eq_raw_div_degree p T
        ⟨(G.pairData i).place.1, (G.pairData i).place.2⟩
    _ = (∑ i, -Real.log (Corollary312GroupedSourceQFactor p T G i)) /
        (Module.finrank ℚ K : ℝ) := by
      rw [← Finset.mul_sum]
      ring

theorem Corollary312QPilotSourceIndexBridge.rawSourceQLogSum_eq_degree_mul_absLogQ
    {T : Corollary312Data K O p} {V : Corollary312VolumeData p T}
    {P : Corollary312QPilotData p T} {Q : Corollary312TateQFamily p T V}
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell)
    (B : Corollary312QPilotSourceIndexBridge p T V P Q) :
    Corollary312RawSourceQLogSum p T Q.grouping =
      (Module.finrank ℚ K : ℝ) * P.absLogQ p := by
  have h := B.absLogQ_eq_degreeNormalizedSourceQLogSum p hOrder hRaw hEll
  rw [degreeNormalizedSourceQLogSum_eq_raw_div_degree] at h
  have hDegree : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    ne_of_gt Arithmetic.finrank_pos
  have hMul := (eq_div_iff hDegree).mp h
  calc
    Corollary312RawSourceQLogSum p T Q.grouping =
        P.absLogQ p * (Module.finrank ℚ K : ℝ) := hMul.symm
    _ = (Module.finrank ℚ K : ℝ) * P.absLogQ p := mul_comm _ _

end JoshiTeich.Act1Scene1
