import ArithmeticTeichmullerSpaces.Act1Scene1.QNormDegreeBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: JT-ATS-III-COR312-PAPER-Q-NORMALIZATION
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`th:moccor-Mochizuki-form2` (3617--3632), `cor:cor312` (3647--3650), and
the explicit `C_p` normalization at 1748--1754 and 2086--2095; completion norm
law: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`,
`norm_eq_zpow_of_valued` and `valued_eq_of_isUniformizer`.
fidelity: identifies the paper's local absolute value, normalized by
`|uniformizer| = p^{-1}`, with the completion norm raised to `1 / inertDeg`;
the actual paper-place carrier and completion comparison remain open
boundary: Scene1/Derived

The completion norm gives a uniformizer norm `p^{-inertDeg}`. The paper's
chosen `C_p` normalization gives `p^{-1}`. This file records the local
residue-degree correction and its exact relation to the IUT q-pilot weight.
-/

noncomputable def Corollary312PaperNormalizedSourceQFactor
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (i : Corollary312SourceQIndex p T) : ℝ :=
  (Corollary312SourceQFactor p T i) ^
    (1 / (Arithmetic.inertDeg i.1 : ℝ))

theorem paperNormalizedSourceQFactor_log_eq_raw_div_residueDegree
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (i : Corollary312SourceQIndex p T) :
    -Real.log (Corollary312PaperNormalizedSourceQFactor p T i) =
      (1 / (Arithmetic.inertDeg i.1 : ℝ)) *
        (-Real.log (Corollary312SourceQFactor p T i)) := by
  have hDegree : (0 : ℝ) < Arithmetic.inertDeg i.1 := by
    exact_mod_cast Arithmetic.inertDeg_pos i.1
  have hRaw : 0 < Corollary312SourceQFactor p T i := by
    unfold Corollary312SourceQFactor
    exact Real.rpow_pos_of_pos
      (T.scene1.input_laws.first_axiom.q_norm_positive i.1 i.2) _
  unfold Corollary312PaperNormalizedSourceQFactor
  rw [Real.log_rpow hRaw]
  ring

theorem paperNormalizedSourceQFactor_log_eq_qOrder_mul_log_residueChar
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell)
    (i : Corollary312SourceQIndex p T)
    (hi : i.1 ∈ Q.badFinset) :
    -Real.log (Corollary312PaperNormalizedSourceQFactor p T i) =
      (1 / (2 * (T.ell : ℝ))) *
        ((T.scene1.data.link.tate.qOrder i.1 : ℝ) *
          Real.log (Arithmetic.residueChar i.1)) := by
  have hRawLog :=
    TateOrderNormCompatibility.qFactor_log_eq_order_mul
      (K := K) (O := O) p T.ell T.scene1.data.link
      T.scene1.input_laws.tate_parameter Q.compatibility hOrder hEll
      i.1 i.2
  have hRawFactorLog :
      -Real.log (Corollary312SourceQFactor p T i) =
        (1 / (2 * (T.ell : ℝ))) *
          ((T.scene1.data.link.tate.qOrder i.1 : ℝ) *
            -Real.log (hOrder.uniformizerNorm i.1)) := by
    simpa [Corollary312SourceQFactor] using hRawLog
  rw [paperNormalizedSourceQFactor_log_eq_raw_div_residueDegree
    (p := p) T i, hRawFactorLog,
    hNorm.uniformizer_log_eq_residueDegree_log i.1 hi]
  have hDegree : (Arithmetic.inertDeg i.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.inertDeg_pos i.1).ne'
  field_simp

theorem qPilotNormalizedLogTerm_eq_weightedPaperNormalizedSourceQFactorLog
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell)
    (i : Corollary312SourceQIndex p T)
    (hi : i.1 ∈ Q.badFinset) :
    Q.normalizedLogTerm p i.1 =
      Arithmetic.qPilotWeight i.1 *
        -Real.log (Corollary312PaperNormalizedSourceQFactor p T i) := by
  rw [paperNormalizedSourceQFactor_log_eq_qOrder_mul_log_residueChar
    (p := p) T Q hOrder hNorm hEll i hi]
  unfold Corollary312QPilotData.normalizedLogTerm
  rw [hNorm.weight_eq_qPilotWeight i.1]
  ring

/-!
The local paper-normalized identity can be summed over the q-pilot carrier.
This is deliberately a weighted statement: it does not identify the result
with the paper's unweighted `(p,w)` sum or construct `V_p^oss`.
-/
theorem absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell) :
    Q.absLogQ p =
      ∑ w : Q.badFinset,
        Arithmetic.qPilotWeight w.1 *
          -Real.log
            (Corollary312PaperNormalizedSourceQFactor p T
              (show Corollary312SourceQIndex p T from
                ⟨w.1, Q.mem_bad p w.2⟩)) := by
  classical
  have hNormalize :
      Q.absLogQ p =
        ∑ w ∈ Q.badFinset.attach, Q.normalizedLogTerm p w.1 := by
    unfold Corollary312QPilotData.absLogQ Corollary312QPilotData.logQ
    calc
      (∑ w ∈ Q.badFinset.attach,
          Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
            Real.log (Arithmetic.residueChar w.1)) /
          (2 * (T.ell : ℝ)) =
          (1 / (2 * (T.ell : ℝ))) *
            ∑ w ∈ Q.badFinset.attach,
              Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
                Real.log (Arithmetic.residueChar w.1) := by ring
      _ = ∑ w ∈ Q.badFinset.attach,
          (1 / (2 * (T.ell : ℝ))) *
            (Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
              Real.log (Arithmetic.residueChar w.1)) := by
        rw [Finset.mul_sum]
      _ = ∑ w ∈ Q.badFinset.attach, Q.normalizedLogTerm p w.1 := by
        rfl
  calc
    Q.absLogQ p =
        ∑ w ∈ Q.badFinset.attach, Q.normalizedLogTerm p w.1 := hNormalize
    _ = ∑ w ∈ Q.badFinset.attach,
        Arithmetic.qPilotWeight w.1 *
          -Real.log
            (Corollary312PaperNormalizedSourceQFactor p T
              (show Corollary312SourceQIndex p T from
                ⟨w.1, Q.mem_bad p w.2⟩)) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact qPilotNormalizedLogTerm_eq_weightedPaperNormalizedSourceQFactorLog
        p T Q hOrder hNorm hEll
        (show Corollary312SourceQIndex p T from
          ⟨w.1, Q.mem_bad p w.2⟩) w.2
    _ = ∑ w : Q.badFinset,
        Arithmetic.qPilotWeight w.1 *
          -Real.log
            (Corollary312PaperNormalizedSourceQFactor p T
              (show Corollary312SourceQIndex p T from
                ⟨w.1, Q.mem_bad p w.2⟩)) := by
      simp

/-! The preceding weighted logarithmic identity has a finite-product form.  The
product below is still the actual q-pilot carrier with explicit arithmetic
weights; it is not the paper's unweighted representative product or its
theta-volume. -/
noncomputable def weightedPaperNormalizedSourceQFactor
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) (w : Q.badFinset) : ℝ :=
  Corollary312PaperNormalizedSourceQFactor p T
    (show Corollary312SourceQIndex p T from
      ⟨w.1, Q.mem_bad p w.2⟩)

noncomputable def weightedPaperNormalizedSourceQFactorProduct
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) : ℝ :=
  ∏ w : Q.badFinset,
    weightedPaperNormalizedSourceQFactor p T Q w ^ Arithmetic.qPilotWeight w.1

theorem weightedPaperNormalizedSourceQFactorProduct_pos
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) :
    0 < weightedPaperNormalizedSourceQFactorProduct p T Q := by
  unfold weightedPaperNormalizedSourceQFactorProduct
  apply Finset.prod_pos
  intro w hw
  have hq : 0 < Corollary312SourceQFactor p T
      (show Corollary312SourceQIndex p T from
        ⟨w.1, Q.mem_bad p w.2⟩) := by
    unfold Corollary312SourceQFactor
    exact Real.rpow_pos_of_pos
      (T.scene1.input_laws.first_axiom.q_norm_positive w.1 (Q.mem_bad p w.2)) _
  unfold weightedPaperNormalizedSourceQFactor
  exact Real.rpow_pos_of_pos
    (by
      unfold Corollary312PaperNormalizedSourceQFactor
      exact Real.rpow_pos_of_pos hq _) _

theorem weightedPaperNormalizedSourceQFactorProduct_negLog_eq_absLogQ
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell) :
    -Real.log (weightedPaperNormalizedSourceQFactorProduct p T Q) = Q.absLogQ p := by
  have hfactor : ∀ w : Q.badFinset, 0 <
      weightedPaperNormalizedSourceQFactor p T Q w := by
    intro w
    have hq : 0 < Corollary312SourceQFactor p T
        (show Corollary312SourceQIndex p T from
          ⟨w.1, Q.mem_bad p w.2⟩) := by
      unfold Corollary312SourceQFactor
      exact Real.rpow_pos_of_pos
        (T.scene1.input_laws.first_axiom.q_norm_positive w.1 (Q.mem_bad p w.2)) _
    unfold weightedPaperNormalizedSourceQFactor
    exact Real.rpow_pos_of_pos hq _
  calc
    -Real.log (weightedPaperNormalizedSourceQFactorProduct p T Q) =
        ∑ w : Q.badFinset,
          Arithmetic.qPilotWeight w.1 *
            -Real.log (weightedPaperNormalizedSourceQFactor p T Q w) := by
      unfold weightedPaperNormalizedSourceQFactorProduct
      rw [Real.log_prod (fun w _ =>
        (Real.rpow_pos_of_pos (hfactor w) _).ne')]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Real.log_rpow (hfactor w)]
      ring
    _ = Q.absLogQ p := by
      simpa [weightedPaperNormalizedSourceQFactor] using
        (absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum
          p T Q hOrder hNorm hEll).symm

theorem weightedPaperNormalizedSourceQFactorProduct_eq_exp_neg_absLogQ
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell) :
    weightedPaperNormalizedSourceQFactorProduct p T Q =
      Real.exp (-Q.absLogQ p) := by
  have hneg := weightedPaperNormalizedSourceQFactorProduct_negLog_eq_absLogQ
    p T Q hOrder hNorm hEll
  calc
    weightedPaperNormalizedSourceQFactorProduct p T Q =
        Real.exp (Real.log (weightedPaperNormalizedSourceQFactorProduct p T Q)) :=
      (Real.exp_log (weightedPaperNormalizedSourceQFactorProduct_pos p T Q)).symm
    _ = Real.exp (-Q.absLogQ p) := by
      congr 1
      linarith

end JoshiTeich.Act1Scene1
