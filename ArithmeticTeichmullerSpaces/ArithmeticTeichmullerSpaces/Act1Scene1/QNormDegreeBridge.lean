import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-DEGREE-ADAPTER
source: `iut`: `refer/iut/Iut/Concrete/ThetaRegion.lean`
(`QPilotInputs.qPilot`), `refer/iut/Iut/Concrete/LocalTheory.lean`
(`inertDeg` and finite-place norm), and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`
(`norm_eq_zpow_of_valued`, `valued_eq_of_isUniformizer`);
target-side q-factor: `JoshiTeich: refer/JoshiTeich/index-Arithmetic
Teichmuller Spaces 3.md`, `cor:cor312` (3647--3650)
fidelity: explicit degree adapter for the q-pilot/raw-norm mismatch;
the adapter is a candidate Scene1 bridge and does not change the current
raw-q-factor target
boundary: Scene1/Derived

The current source q-factor uses the raw mathlib finite-place norm.  The IUT
q-pilot uses the arithmetic weight `inertDeg / [K : ℚ]`.  This file records the
only degree normalization needed to compare those presentations.  The raw
uniformizer logarithm law remains an explicit source condition; it is not
inferred from the target inequality.
-/

/-! The q-factor after the global degree normalization required by the IUT
q-pilot weight.  The existing `Corollary312SourceQFactor` is deliberately left
unchanged until the statement-freeze review decides which presentation is the
literal target. -/
noncomputable def Corollary312DegreeNormalizedSourceQFactor
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (i : Corollary312SourceQIndex p T) : ℝ :=
  (Corollary312SourceQFactor p T i) ^
    (1 / (Module.finrank ℚ K : ℝ))

structure Corollary312RawQNormDegreeNormalization
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (Q : Corollary312QPilotData p T) : Prop where
  /-- The q-pilot carrier uses the arithmetic degree weight from `iut`. -/
  weight_eq_qPilotWeight :
    ∀ w, Q.weight w = Arithmetic.qPilotWeight w
  /-- The raw finite-place norm of a uniformizer carries residue degree. -/
  uniformizer_log_eq_residueDegree_log :
    ∀ w ∈ Q.badFinset,
      -Real.log (hOrder.uniformizerNorm w) =
        (Arithmetic.inertDeg w : ℝ) *
          Real.log (Arithmetic.residueChar w)

theorem degreeNormalizedSourceQFactor_log_eq_raw_div_degree
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (i : Corollary312SourceQIndex p T) :
    -Real.log (Corollary312DegreeNormalizedSourceQFactor p T i) =
      (1 / (Module.finrank ℚ K : ℝ)) *
        (-Real.log (Corollary312SourceQFactor p T i)) := by
  have hDegree : (0 : ℝ) < Module.finrank ℚ K :=
    Arithmetic.finrank_pos
  have hRaw : 0 < Corollary312SourceQFactor p T i := by
    unfold Corollary312SourceQFactor
    exact Real.rpow_pos_of_pos
      (T.scene1.input_laws.first_axiom.q_norm_positive i.1 i.2) _
  unfold Corollary312DegreeNormalizedSourceQFactor
  rw [Real.log_rpow hRaw]
  ring

namespace Corollary312QPilotData

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable (Q : Corollary312QPilotData p T)

theorem normalizedLogTerm_eq_degreeNormalizedSourceQFactorLog
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell)
    (w : NumberField.FinitePlace K)
    (hw : w ∈ Q.badFinset) :
    Q.normalizedLogTerm p w =
      -Real.log
        (Corollary312DegreeNormalizedSourceQFactor p T
          (show Corollary312SourceQIndex p T from
            ⟨w, Q.mem_bad p hw⟩)) := by
  have hLocal :=
    TateOrderNormCompatibility.qFactor_log_eq_order_mul
      (K := K) (O := O) p T.ell T.scene1.data.link
      T.scene1.input_laws.tate_parameter Q.compatibility hOrder hEll
      w (Q.mem_bad p hw)
  have hDegree :=
    degreeNormalizedSourceQFactor_log_eq_raw_div_degree
      (K := K) (O := O) p T
      (show Corollary312SourceQIndex p T from
            ⟨w, Q.mem_bad p hw⟩)
  have hRawFactor :
      -Real.log
          (Corollary312SourceQFactor p T
            (show Corollary312SourceQIndex p T from
              ⟨w, Q.mem_bad p hw⟩)) =
        (1 / (2 * (T.ell : ℝ))) *
          ((T.scene1.data.link.tate.qOrder w : ℝ) *
            -Real.log (hOrder.uniformizerNorm w)) := by
    simpa [Corollary312SourceQFactor] using hLocal
  calc
    Q.normalizedLogTerm p w =
        (1 / (Module.finrank ℚ K : ℝ)) *
          (-Real.log
            (Corollary312SourceQFactor p T
              (show Corollary312SourceQIndex p T from
                ⟨w, Q.mem_bad p hw⟩))) := by
      unfold normalizedLogTerm
      rw [hRawFactor]
      rw [hNorm.uniformizer_log_eq_residueDegree_log w hw]
      rw [hNorm.weight_eq_qPilotWeight w]
      unfold Arithmetic.qPilotWeight
      ring
    _ = -Real.log
        (Corollary312DegreeNormalizedSourceQFactor p T
          (show Corollary312SourceQIndex p T from
            ⟨w, Q.mem_bad p hw⟩)) := hDegree.symm

end Corollary312QPilotData

end JoshiTeich.Act1Scene1
