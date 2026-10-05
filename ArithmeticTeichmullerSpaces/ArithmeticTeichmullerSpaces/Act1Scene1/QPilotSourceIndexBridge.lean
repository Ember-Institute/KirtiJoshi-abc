import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotSourceBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.TransferQAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe uK

/-- The canonical `(p,w)` grouping ported from the `iut` place layer.  The
residue characteristic supplies the rational-prime label and its ideal-over
relation; only the admissible-prime coprimality and the target/source index
equivalence remain construction inputs. -/
noncomputable def Corollary312SourceQGrouping.ofPlaceIndex
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (hIndex : T.qIndex ≃ Corollary312SourceQIndex p T)
    (hCoprime : ∀ w : Corollary312SourceQIndex p T,
      Nat.Coprime T.ell (T.scene1.data.link.tate.qOrder w.1)) :
    Corollary312SourceQGrouping p T := by
  classical
  refine
    { pair := Corollary312SourceQIndex p T
      pairFintype := Fintype.ofFinset T.scene1.data.link.places (fun _ => Iff.rfl)
      pairData := fun w => ?_
      indexEquiv := hIndex }
  exact
    { rationalPrime := Arithmetic.residueChar w.1
      rationalPrime_prime := Arithmetic.residueChar_prime w.1
      place := w
      rationalPrime_eq_residueChar := rfl
      rationalPrime_liesOver := Arithmetic.residueChar_liesOver w.1
      tate_place := by
        rw [← hCompat.places_eq]
        exact w.2
      q_order_coprime := hCoprime w }

/-!
source-id: IUT-COR312-Q-PILOT-SOURCE-INDEX
source: `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean`,
`refer/iut/Iut/Cor312/ThetaData/Places.lean`, and
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`; target-side finite grouping:
`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`cor:cor312` (3647--3650)
fidelity: finite-index and finite-sum bridge from the adapted q-pilot carrier
to the explicit source q-family; the equivalence and place compatibility are
construction fields, not inferred from the Prologue
boundary: Scene1/Derived

The q-pilot and source q-family use different finite carriers.  This module
records the missing finite equivalence explicitly and then lifts the local
normalization from `QPilotSourceBridge` to the global finite sum.
-/

structure Corollary312QPilotSourceIndexBridge
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (P : Corollary312QPilotData p T)
    (Q : Corollary312TateQFamily p T V) where
  /-- The q-pilot bad-place subtype is identified with the source grouping. -/
  placePairEquiv : P.badFinset ≃ Q.grouping.pair
  /-- The grouping pair carries the same finite place as the q-pilot index. -/
  pair_place_eq : ∀ w : P.badFinset,
    (Q.grouping.pairData (placePairEquiv w)).place.1 = w.1

/-!
The q-pilot and Tate q-family already carry enough finite equivalences to
construct the bridge canonically.  This adapter keeps the place equality
visible while removing the need to repeat the same subtype transport at each
call site.
-/
noncomputable def Corollary312QPilotSourceIndexBridge.ofGrouping
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (P : Corollary312QPilotData p T)
    (Q : Corollary312TateQFamily p T V) :
    Corollary312QPilotSourceIndexBridge p T V P Q := by
  let toSource : P.badFinset → Corollary312SourceQIndex p T :=
    fun w => ⟨w.1, P.mem_bad p w.2⟩
  let toPair : P.badFinset → Q.grouping.pair :=
    fun w => Q.grouping.indexEquiv (Q.indexEquiv.symm (toSource w))
  let fromPair : Q.grouping.pair → P.badFinset := fun i =>
    let s := Q.indexEquiv (Q.grouping.indexEquiv.symm i)
    ⟨s.1, by
      simpa [P.badFinset_spec] using s.2⟩
  let e : P.badFinset ≃ Q.grouping.pair :=
    { toFun := toPair
      invFun := fromPair
      left_inv := by
        intro w
        apply Subtype.ext
        simp only [fromPair, toPair, Equiv.symm_apply_apply]
        simpa [toSource] using
          congrArg Subtype.val (Q.indexEquiv.apply_symm_apply (toSource w))
      right_inv := by
        intro i
        dsimp [toPair]
        conv_rhs => rw [← Q.grouping.indexEquiv.apply_symm_apply i]
        have hSource :
            toSource (fromPair i) =
              Q.indexEquiv (Q.grouping.indexEquiv.symm i) := by
          apply Subtype.ext
          rfl
        have hArgs :
            Q.indexEquiv.symm (toSource (fromPair i)) =
              Q.grouping.indexEquiv.symm i := by
          rw [hSource, Q.indexEquiv.symm_apply_apply]
        exact congrArg Q.grouping.indexEquiv hArgs }
  refine
    { placePairEquiv := e
      pair_place_eq := ?_ }
  intro w
  have h := Q.grouping_place_eq (Q.indexEquiv.symm (toSource w))
  change
    (Q.grouping.pairData
      (Q.grouping.indexEquiv (Q.indexEquiv.symm (toSource w)))).place.1 = w.1
  rw [h]
  simpa [toSource] using
    congrArg Subtype.val (Q.indexEquiv.apply_symm_apply (toSource w))

namespace Corollary312QPilotSourceIndexBridge

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}
variable {V : Corollary312VolumeData p T}
variable {P : Corollary312QPilotData p T}
variable {Q : Corollary312TateQFamily p T V}

private theorem groupedFactor_eq_sourceFactor
    (B : Corollary312QPilotSourceIndexBridge p T V P Q)
    (w : P.badFinset) :
    Corollary312GroupedSourceQFactor p T Q.grouping (B.placePairEquiv w) =
      Corollary312SourceQFactor p T
        (show Corollary312SourceQIndex p T from
          ⟨w.1, P.mem_bad p w.2⟩) := by
  unfold Corollary312GroupedSourceQFactor Corollary312SourceQFactor
  rw [B.pair_place_eq w]

theorem absLogQ_eq_sourceQLogSum
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312QPilotSourceNormalization p T hOrder P)
    (hEll : 0 < T.ell)
    (B : Corollary312QPilotSourceIndexBridge p T V P Q) :
    P.absLogQ p = Corollary312SourceQLogSum p T V Q := by
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
          (Corollary312GroupedSourceQFactor p T Q.grouping
            (B.placePairEquiv w)) := by
    have hLocal :=
      Corollary312QPilotData.normalizedLogTerm_eq_sourceQFactorLog
        p P hOrder hNorm hEll w.1 w.2
    rw [B.groupedFactor_eq_sourceFactor (w := w)]
    exact hLocal
  calc
    P.absLogQ p =
        ∑ w ∈ P.badFinset.attach, P.normalizedLogTerm p w.1 := hNormalize
    _ = ∑ w : P.badFinset,
        -Real.log
          (Corollary312GroupedSourceQFactor p T Q.grouping
            (B.placePairEquiv w)) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hTerm w
    _ = ∑ i : Q.grouping.pair,
        -Real.log (Corollary312GroupedSourceQFactor p T Q.grouping i) := by
      simpa using B.placePairEquiv.sum_comp
        (fun i => -Real.log (Corollary312GroupedSourceQFactor p T Q.grouping i))
    _ = Corollary312SourceQLogSum p T V Q := by
      rfl

end Corollary312QPilotSourceIndexBridge

end JoshiTeich.Act1Scene1
