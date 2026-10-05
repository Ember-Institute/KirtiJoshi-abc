import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-SOURCE-NORMALIZATION
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData.logQ`,
`QPilotData.absLogQ`) and `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean`;
target-side source q-factor: `JoshiTeich: refer/JoshiTeich/index-Arithmetic
Teichmuller Spaces 3.md`, `cor:cor312` (3647--3650)
fidelity: local normalized q-pilot term; the arithmetic weight and the
weighted uniformizer normalization are explicit conditions, not hidden constructions
boundary: Scene1/Derived

The q-pilot formula and the q-family formula use different presentations of a
local term.  This module records the exact local conversion.  It intentionally
does not identify the finite sums: the place-to-`(p,w)` equivalence and its
finite-support proof remain a separate construction obligation.
-/

structure Corollary312QPilotSourceNormalization
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (Q : Corollary312QPilotData p T) : Prop where
  /-- The uniformizer norm carries the q-divisor's arithmetic-degree weight. -/
  uniformizer_log_eq_weighted_residueChar_log :
    ∀ w ∈ Q.badFinset,
      -Real.log (hOrder.uniformizerNorm w) =
        Q.weight w * Real.log (Arithmetic.residueChar w)

namespace Corollary312QPilotData

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

variable (Q : Corollary312QPilotData p T)

/-- The q-pilot local contribution after the `1/(2*ell)` normalization. -/
noncomputable def normalizedLogTerm
    (w : NumberField.FinitePlace K) : ℝ :=
  (1 / (2 * (T.ell : ℝ))) *
    (Q.weight w * (T.scene1.data.link.tate.qOrder w : ℝ) *
      Real.log (Arithmetic.residueChar w))

theorem normalizedLogTerm_eq_sourceQFactorLog
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312QPilotSourceNormalization p T hOrder Q)
    (hEll : 0 < T.ell)
    (w : NumberField.FinitePlace K)
    (hw : w ∈ Q.badFinset) :
    Q.normalizedLogTerm p w =
      -Real.log
        (Corollary312SourceQFactor p T
          (show Corollary312SourceQIndex p T from
            ⟨w, Q.mem_bad p hw⟩)) := by
  unfold normalizedLogTerm
  have hLocal :=
    TateOrderNormCompatibility.qFactor_log_eq_order_mul
      (K := K) (O := O) p T.ell T.scene1.data.link
      T.scene1.input_laws.tate_parameter Q.compatibility hOrder hEll
      w (Q.mem_bad p hw)
  calc
    Q.normalizedLogTerm p w =
        (1 / (2 * (T.ell : ℝ))) *
          ((T.scene1.data.link.tate.qOrder w : ℝ) *
            -Real.log (hOrder.uniformizerNorm w)) := by
      unfold normalizedLogTerm
      rw [hNorm.uniformizer_log_eq_weighted_residueChar_log w hw]
      ring
    _ = -Real.log
        (Corollary312SourceQFactor p T
          (show Corollary312SourceQIndex p T from
            ⟨w, Q.mem_bad p hw⟩)) := by
      simpa [Corollary312SourceQFactor] using hLocal.symm

end Corollary312QPilotData

end JoshiTeich.Act1Scene1
