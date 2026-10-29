import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDegreePaperFactorBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-PAPER-FACTOR-PRODUCT-BRIDGE
source: the finite q-pilot carrier and the local degree/paper factor power
conversion proved in `IutInitialThetaDegreePaperFactorBridge.lean`.
fidelity: lifts the local three-layer q-factor equality to the complete finite
actual source product. The carrier remains the supplied q-pilot carrier; no
paper representative or theta-volume identity is inferred.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators
universe u
noncomputable section

def degreeNormalizedSourceQFactorProduct
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) : ℝ :=
  ∏ w : Q.badFinset,
    Corollary312DegreeNormalizedSourceQFactor p T
      (show Corollary312SourceQIndex p T from ⟨w.1, Q.mem_bad p w.2⟩)

def paperNormalizedSourceQFactorProduct_rpow
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) : ℝ :=
  ∏ w : Q.badFinset,
    Corollary312PaperNormalizedSourceQFactor p T
      (show Corollary312SourceQIndex p T from ⟨w.1, Q.mem_bad p w.2⟩) ^
        ((Arithmetic.inertDeg w.1 : ℝ) /
          (Module.finrank ℚ K : ℝ))

theorem degreeNormalizedSourceQFactorProduct_pos
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) :
    0 < degreeNormalizedSourceQFactorProduct p T Q := by
  unfold degreeNormalizedSourceQFactorProduct
  exact Finset.prod_pos fun w _ => by
    unfold Corollary312DegreeNormalizedSourceQFactor
    exact Real.rpow_pos_of_pos
      (by
        unfold Corollary312SourceQFactor
        exact Real.rpow_pos_of_pos
          (T.scene1.input_laws.first_axiom.q_norm_positive w.1 (Q.mem_bad p w.2)) _)
      _

theorem degreeNormalizedSourceQFactorProduct_negLog_eq_sum
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) :
    -Real.log (degreeNormalizedSourceQFactorProduct p T Q) =
      ∑ w : Q.badFinset,
        -Real.log (Corollary312DegreeNormalizedSourceQFactor p T
          (show Corollary312SourceQIndex p T from ⟨w.1, Q.mem_bad p w.2⟩)) := by
  unfold degreeNormalizedSourceQFactorProduct
  rw [Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
  · intro w hw
    unfold Corollary312DegreeNormalizedSourceQFactor
    exact Real.rpow_pos_of_pos
      (by
        unfold Corollary312SourceQFactor
        exact Real.rpow_pos_of_pos
          (T.scene1.input_laws.first_axiom.q_norm_positive w.1 (Q.mem_bad p w.2)) _)
      _ |>.ne'

theorem paperNormalizedSourceQFactorProduct_rpow_eq_weightedPaperNormalizedSourceQFactorProduct
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) :
    paperNormalizedSourceQFactorProduct_rpow p T Q =
      weightedPaperNormalizedSourceQFactorProduct p T Q := by
  unfold paperNormalizedSourceQFactorProduct_rpow
    weightedPaperNormalizedSourceQFactorProduct
    weightedPaperNormalizedSourceQFactor
  apply Finset.prod_congr rfl
  intro w hw
  unfold Arithmetic.qPilotWeight
  rfl

theorem paperNormalizedSourceQFactorProduct_rpow_eq_exp_neg_absLogQ
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell) :
    paperNormalizedSourceQFactorProduct_rpow p T Q =
      Real.exp (-(Q.absLogQ p)) := by
  rw [paperNormalizedSourceQFactorProduct_rpow_eq_weightedPaperNormalizedSourceQFactorProduct
    p T Q]
  exact weightedPaperNormalizedSourceQFactorProduct_eq_exp_neg_absLogQ
    p T Q hOrder hNorm hEll

theorem degreeNormalizedSourceQFactorProduct_eq_paperNormalizedSourceQFactorProduct_rpow
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T) :
    degreeNormalizedSourceQFactorProduct p T Q =
      paperNormalizedSourceQFactorProduct_rpow p T Q := by
  unfold degreeNormalizedSourceQFactorProduct paperNormalizedSourceQFactorProduct_rpow
  apply Finset.prod_congr rfl
  intro w hw
  exact degreeNormalizedSourceQFactor_eq_paperNormalizedSourceQFactor_rpow
    p T ⟨w.1, Q.mem_bad p w.2⟩

theorem degreeNormalizedSourceQFactorProduct_eq_exp_neg_absLogQ
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell) :
    degreeNormalizedSourceQFactorProduct p T Q =
      Real.exp (-(Q.absLogQ p)) := by
  rw [degreeNormalizedSourceQFactorProduct_eq_paperNormalizedSourceQFactorProduct_rpow
    p T Q]
  exact paperNormalizedSourceQFactorProduct_rpow_eq_exp_neg_absLogQ
    p T Q hOrder hNorm hEll

theorem degreeNormalizedSourceQFactorProduct_negLog_eq_absLogQ
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (Q : Corollary312QPilotData p T)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder Q)
    (hEll : 0 < T.ell) :
    -Real.log (degreeNormalizedSourceQFactorProduct p T Q) = Q.absLogQ p := by
  rw [degreeNormalizedSourceQFactorProduct_eq_exp_neg_absLogQ
    p T Q hOrder hNorm hEll, Real.log_exp]
  ring

end
end JoshiTeich.Act1Scene1
