import ArithmeticTeichmullerSpaces.Act1Scene1.IutQPilotAdapter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateValuation

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-COMPLETION-ADAPTER
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`localCompletion`, `tate`, `unif`, `unif_isUniformizer`, `q_order_coprime`,
and `qOrder`; local norm/order transfer is ported in `IutTateValuation.lean`.
fidelity: constructs the base completion-valued q-pilot source from the existing
Scene1 q-pilot source and proves that the chosen-uniformizer order is its source
order. It still depends on the source-to-link parameter and order compatibility
fields and does not construct a real `InitialThetaData`.
boundary: Scene1/Derived
-/

namespace IutQPilotSource

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

lemma badFinset_mem_badPlacesOver (S : IutQPilotSource p T)
    (w : S.badFinset) : w.1 ∈ S.badPlacesOver := by
  have hwfin : w.1 ∈ (↑S.badFinset : Set (NumberField.FinitePlace K)) :=
    Finset.mem_coe.mpr w.2
  rw [S.badFinset_spec] at hwfin
  exact hwfin

noncomputable def toBaseQPilotSource (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutBaseQPilotSource K T.ell := by
  refine
    { badPlaces := S.badPlacesOver
      badFinset := S.badFinset
      badFinset_spec := S.badFinset_spec
      weight := Arithmetic.qPilotWeight
      weight_eq_qPilotWeight := fun _ => rfl
      tateParameter := fun w =>
        NumberField.FinitePlace.embedding w.1.maximalIdeal (S.tateParameter w.1)
      tateParameter_ne_zero := ?_
      tateParameter_norm_lt_one := ?_ }
  · intro w
    apply (map_ne_zero _).2
    exact S.tateParameter_ne_zero w.1 (S.badFinset_mem_badPlacesOver p w)
  · intro w
    have hwBad := S.badFinset_mem_badPlacesOver p w
    have hwLink := (S.mem_badPlacesOver_iff_link p w.1).mp hwBad
    have hwTate : w.1 ∈ T.scene1.data.link.tate.places := by
      rw [← hCompat.places_eq]
      exact hwLink
    calc
      ‖NumberField.FinitePlace.embedding w.1.maximalIdeal (S.tateParameter w.1)‖ =
          ‖NumberField.FinitePlace.embedding w.1.maximalIdeal
            (T.scene1.data.link.tate.parameter w.1)‖ := by
              rw [S.tateParameter_eq_link w.1 hwBad]
      _ = T.scene1.data.link.tate.norm w.1 := by
        rw [NumberField.FinitePlace.norm_embedding_eq]
        exact (T.scene1.input_laws.tate_parameter.norm_eq w.1 hwTate).symm
      _ < 1 := T.scene1.input_laws.tate_parameter.norm_lt_one w.1 hwTate

lemma completionParameter_norm_eq_chosenUniformizer_pow_order
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (w : NumberField.FinitePlace K) (hw : w ∈ S.badPlacesOver) :
    ‖NumberField.FinitePlace.embedding w.maximalIdeal (S.tateParameter w)‖ =
      ‖S.uniformizer w hw‖ ^ S.qOrder w := by
  calc
    ‖NumberField.FinitePlace.embedding w.maximalIdeal (S.tateParameter w)‖ =
        w (S.tateParameter w) := NumberField.FinitePlace.norm_embedding_eq w _
    _ = S.orderCompatibility.uniformizerNorm w ^ S.qOrder w :=
      S.source_norm_eq_uniformizer_pow_order p hCompat w hw
    _ = ‖S.uniformizer w hw‖ ^ S.qOrder w := by
      rw [← S.uniformizerNorm_eq_chosenNorm w hw]

noncomputable def toCompletionTateValuation
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutCompletionTateValuation (S.toBaseQPilotSource p hCompat) := by
  let B := S.toBaseQPilotSource p hCompat
  refine
    { uniformizer := fun w => S.uniformizer w.1 (S.badFinset_mem_badPlacesOver p w)
      uniformizer_isCompletionUniformizer := fun w =>
        S.uniformizer_isCompletionUniformizer w.1 (S.badFinset_mem_badPlacesOver p w)
      orderedQOrder_coprime := ?_ }
  intro w
  have hwBad := S.badFinset_mem_badPlacesOver p w
  have hOrder := iutCompletionUniformizerQOrder_eq_of_norm_eq
    w.1 (B.tateParameter w) (B.tateParameter_ne_zero w)
    (B.tateParameter_norm_lt_one w)
    (S.uniformizer w.1 hwBad)
    (S.uniformizer_isCompletionUniformizer w.1 hwBad)
    (S.qOrder w.1)
    (S.completionParameter_norm_eq_chosenUniformizer_pow_order p hCompat
      w.1 hwBad)
  change Nat.Coprime T.ell
    (iutCompletionUniformizerQOrder w.1 (B.tateParameter w)
      (B.tateParameter_ne_zero w) (S.uniformizer w.1 hwBad)
      (S.uniformizer_isCompletionUniformizer w.1 hwBad))
  rw [hOrder]
  exact S.qOrder_coprime w.1 hwBad

lemma toCompletionTateValuation_order_eq_qOrder
    (S : IutQPilotSource p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (w : S.badFinset) :
    (S.toCompletionTateValuation p hCompat).orderedQOrder w = S.qOrder w.1 := by
  have hwBad := S.badFinset_mem_badPlacesOver p w
  exact iutCompletionUniformizerQOrder_eq_of_norm_eq
    w.1 ((S.toBaseQPilotSource p hCompat).tateParameter w)
    ((S.toBaseQPilotSource p hCompat).tateParameter_ne_zero w)
    ((S.toBaseQPilotSource p hCompat).tateParameter_norm_lt_one w)
    (S.uniformizer w.1 hwBad)
    (S.uniformizer_isCompletionUniformizer w.1 hwBad)
    (S.qOrder w.1)
    (S.completionParameter_norm_eq_chosenUniformizer_pow_order p hCompat w.1 hwBad)

end IutQPilotSource

end JoshiTeich.Act1Scene1
