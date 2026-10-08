import ArithmeticTeichmullerSpaces.Act1Scene1.QNormDegreeBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

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

end JoshiTeich.Act1Scene1
