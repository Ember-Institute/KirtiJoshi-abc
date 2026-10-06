import ArithmeticTeichmullerSpaces.Act1Scene1.QFamilyBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: JT-ATS-III-COR312-RAW-TARGET
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`cor:cor312` (3647--3650), whose q-term is
`-log |q_w^(1/(2*ell))|_{L'_w}`.
fidelity: the raw finite-place norm presentation is made explicit as a
Scene1 target specification.  The current source carrier is the explicit
Scene1 carrier; identifying it with the paper's `V_p^oss` remains a separate
Initial Theta Data obligation.
boundary: Scene1/Derived

This file closes the target-side q-term ambiguity without changing the
degree-normalized IUT q-pilot adapter.  It proves an exact equivalence between
the abstract `Corollary312` shell and the raw finite grouped q-sum once the
finite index identification and q-log equalities are supplied.  It does not
construct those identifications from the Prologue contracts.
-/

noncomputable def Corollary312RawSourceQLogSum
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (G : Corollary312SourceQGrouping p T) : ℝ :=
  letI := G.pairFintype
  ∑ i, -Real.log (Corollary312GroupedSourceQFactor p T G i)

structure Corollary312RawTargetSpecification
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  /-- The explicit finite `(p,w)` grouping used by the raw target terms. -/
  grouping : Corollary312SourceQGrouping p T
  /-- Every target q-log term is the raw finite-place q-factor term. -/
  qLogTerm_eq : ∀ i,
    T.qLogTerm i =
      -Real.log
        (Corollary312GroupedSourceQFactor p T grouping (grouping.indexEquiv i))

namespace Corollary312RawTargetSpecification

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

theorem qLogSum_eq_rawSourceQLogSum
    (R : Corollary312RawTargetSpecification p T) :
    Corollary312Data.qLogSum p T =
      Corollary312RawSourceQLogSum p T R.grouping := by
  letI := T.qIndexFintype
  letI := R.grouping.pairFintype
  unfold Corollary312Data.qLogSum Corollary312RawSourceQLogSum
  calc
    (∑ i : T.qIndex, T.qLogTerm i) =
        ∑ i : T.qIndex,
          -Real.log
            (Corollary312GroupedSourceQFactor p T R.grouping
              (R.grouping.indexEquiv i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact R.qLogTerm_eq i
    _ = ∑ j : R.grouping.pair,
          -Real.log (Corollary312GroupedSourceQFactor p T R.grouping j) := by
      simpa using R.grouping.indexEquiv.sum_comp
        (fun j => -Real.log (Corollary312GroupedSourceQFactor p T R.grouping j))

end Corollary312RawTargetSpecification

/-!
The proposition below is the exact raw q-term presentation of Corollary 3.12.
It is a target-side alias with a proof of equivalence, not a new assumption.
-/
def Corollary312RawTarget
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (R : Corollary312RawTargetSpecification p T) : Prop :=
  -(1 / (T.ellStar : ℝ)) * |Real.log T.thetaVolume| ≥
    -Corollary312RawSourceQLogSum p T R.grouping

theorem corollary312_iff_rawTarget
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (R : Corollary312RawTargetSpecification p T) :
    Corollary312 p T ↔ Corollary312RawTarget p T R := by
  rw [Corollary312, Corollary312RawTarget,
    R.qLogSum_eq_rawSourceQLogSum p]

end JoshiTeich.Act1Scene1
