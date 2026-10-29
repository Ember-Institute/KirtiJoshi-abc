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

end
end JoshiTeich.Act1Scene1
