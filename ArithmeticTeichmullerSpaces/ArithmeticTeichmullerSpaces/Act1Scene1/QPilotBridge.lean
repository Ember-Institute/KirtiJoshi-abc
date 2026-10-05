import ArithmeticTeichmullerSpaces.Act1Scene1.QNormTateBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-LHS
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` and
`refer/iut/Iut/Concrete/LocalTheory.lean`,
`QPilotData`; semantic normalization: IUT I, Example 3.2(iv), and IUT IV,
Theorem 1.10; the target-side q-family remains sourced from
`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`cor:cor312` (3647--3650)
fidelity: adapted left-hand-side q-pilot carrier; the finite support is the
current Scene1 link-place carrier and is not identified with the paper's
`V_p^oss`
boundary: Scene1/Derived

This file ports the useful computational boundary of `iut`'s `QPilotData`.
The reference implementation deliberately takes the bad-place enumeration and
the normalized arithmetic weights as inputs.  The same honesty boundary is
kept here: the source place set and weights are explicit fields, while the
construction of the admissible `V_p^oss` locus is still a later Scene1 task.
-/

structure Corollary312QPilotData
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  /-- The finite source-place enumeration used by the q-pilot calculation. -/
  badFinset : Finset (NumberField.FinitePlace K)
  /-- The enumeration is exactly the current Scene1 link-place carrier. -/
  badFinset_spec : badFinset = T.scene1.data.link.places
  /-- Normalized arithmetic-degree weight of a source place. -/
  weight : NumberField.FinitePlace K → ℝ
  /-- Source-place weights are positive. -/
  weight_pos : ∀ w ∈ badFinset, 0 < weight w
  /-- The q-norm/Tate place identification consumed by q-order calculations. -/
  compatibility : QNormTateCompatibility T.scene1.data.link

/-- Construct the q-pilot carrier with the normalized finite-place weights used
by the concrete `iut` implementation.  The finite support is the Tate-place
carrier already present in the Scene1 link; `hCompat` identifies it with the
link's place enumeration. -/
noncomputable def Corollary312QPilotData.ofArithmeticWeights
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    Corollary312QPilotData p T := by
  refine
    { badFinset := T.scene1.data.link.places
      badFinset_spec := rfl
      weight := Arithmetic.placeWeight
      weight_pos := ?_
      compatibility := hCompat }
  intro w hw
  exact Arithmetic.placeWeight_pos w

namespace Corollary312QPilotData

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

variable (Q : Corollary312QPilotData p T)

lemma mem_bad {w : NumberField.FinitePlace K} (hw : w ∈ Q.badFinset) :
    w ∈ T.scene1.data.link.places := by
  rw [← Q.badFinset_spec]
  exact hw

lemma mem_tate {w : NumberField.FinitePlace K} (hw : w ∈ Q.badFinset) :
    w ∈ T.scene1.data.link.tate.places := by
  rw [← Q.compatibility.places_eq]
  exact Q.mem_bad p hw

lemma qOrder_pos {w : NumberField.FinitePlace K} (hw : w ∈ Q.badFinset) :
    0 < T.scene1.data.link.tate.qOrder w := by
  exact T.scene1.input_laws.tate_parameter.orderNat_pos w (Q.mem_tate p hw)

/-- The normalized q-divisor degree, weighted by the source-place arithmetic
degree and the residue characteristic. -/
noncomputable def logQ : ℝ :=
  Finset.sum Q.badFinset.attach (fun w =>
    Q.weight w.1 * (T.scene1.data.link.tate.qOrder w.1 : ℝ) *
      Real.log (Arithmetic.residueChar w.1))

/-- The IUT III normalization `|log(q)| = log(q)/(2*ell)`. -/
noncomputable def absLogQ : ℝ := logQ p Q / (2 * (T.ell : ℝ))

/-- The left-hand side carried by the q-pilot source calculation. -/
noncomputable def lhs : ℝ := -absLogQ p Q

lemma logQ_nonneg : 0 ≤ logQ p Q := by
  unfold logQ
  apply Finset.sum_nonneg
  intro w hw
  have hWeight : 0 ≤ Q.weight w.1 := (Q.weight_pos w.1 w.2).le
  have hOrder : 0 ≤ (T.scene1.data.link.tate.qOrder w.1 : ℝ) :=
    (Nat.cast_nonneg _)
  have hPrime : 1 < (Arithmetic.residueChar w.1 : ℝ) := by
    exact_mod_cast (Arithmetic.residueChar_prime w.1).one_lt
  have hLog : 0 ≤ Real.log (Arithmetic.residueChar w.1) :=
    (Real.log_pos hPrime).le
  positivity

end Corollary312QPilotData

end JoshiTeich.Act1Scene1
