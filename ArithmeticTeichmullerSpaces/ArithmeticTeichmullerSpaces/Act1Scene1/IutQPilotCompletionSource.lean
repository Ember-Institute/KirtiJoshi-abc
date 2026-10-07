import ArithmeticTeichmullerSpaces.Act1Scene1.IutQPilotCompletionAdapter

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: IUT-COR312-Q-PILOT-COMPLETION-SOURCE
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`AdmissiblePrimeData.tate`, `unif`, `unif_isUniformizer`, `q_order_coprime`,
and `qOrder`; `refer/iut/Iut/Concrete/ThetaRegion.lean`, `QPilotInputs.qPilot`.
fidelity: assembles the existing completion-valued base q-pilot and its chosen
uniformizer into `IutQPilotSource`. It derives finiteness, positivity, source
coprimality, and the raw norm/order compatibility. Place, parameter, and order
identifications remain explicit; this does not construct `InitialThetaData`.
boundary: Scene1/Derived
-/

namespace IutQPilotSource

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

private def completionIndex
    (B : IutBaseQPilotSource K T.ell)
    (hPlaces : B.badPlaces =
      (↑T.scene1.data.link.places : Set (NumberField.FinitePlace K)))
    (w : NumberField.FinitePlace K)
    (hw : w ∈ T.scene1.data.link.places) : B.badFinset := by
  have hwBad : w ∈ B.badPlaces := by
    rw [hPlaces]
    exact Finset.mem_coe.mpr hw
  have hwFin : w ∈ (↑B.badFinset : Set (NumberField.FinitePlace K)) := by
    rw [B.badFinset_spec]
    exact hwBad
  exact ⟨w, Finset.mem_coe.mp hwFin⟩

private lemma linkMemOfBad
    (B : IutBaseQPilotSource K T.ell)
    (hPlaces : B.badPlaces =
      (↑T.scene1.data.link.places : Set (NumberField.FinitePlace K)))
    (w : NumberField.FinitePlace K) (hw : w ∈ B.badPlaces) :
    w ∈ T.scene1.data.link.places := by
  have hwLink : w ∈ (↑T.scene1.data.link.places : Set (NumberField.FinitePlace K)) := by
    rw [← hPlaces]
    exact hw
  exact Finset.mem_coe.mp hwLink

private noncomputable def completionUniformizerNorm
    (B : IutBaseQPilotSource K T.ell)
    (C : IutCompletionTateValuation B)
    (hPlaces : B.badPlaces =
      (↑T.scene1.data.link.places : Set (NumberField.FinitePlace K)))
    (w : NumberField.FinitePlace K) : ℝ := by
  classical
  exact if hw : w ∈ T.scene1.data.link.places then
    ‖C.uniformizer (completionIndex p B hPlaces w hw)‖ else 1

noncomputable def ofBaseCompletionSource
    (B : IutBaseQPilotSource K T.ell)
    (C : IutCompletionTateValuation B)
    (hPlaces : B.badPlaces =
      (↑T.scene1.data.link.places : Set (NumberField.FinitePlace K)))
    (hParameter : ∀ w : B.badFinset,
      B.tateParameter w =
        T.scene1.data.link.tate.parameter w.1)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutQPilotSource p T := by
  classical
  let hTate := T.scene1.input_laws.tate_parameter
  have hSourceOrder (i : B.badFinset) :
      B.qOrder i = T.scene1.data.link.tate.qOrder i.1 := by
    change Arithmetic.completionQOrder i.1 (B.tateParameter i) =
      Arithmetic.completionQOrder i.1 (T.scene1.data.link.tate.parameter i.1)
    rw [hParameter i]
  have hOrder (i : B.badFinset) :
      C.orderedQOrder i = T.scene1.data.link.tate.qOrder i.1 := by
    calc
      C.orderedQOrder i = B.qOrder i :=
        (C.completionQOrder_eq_orderNat i).symm
      _ = T.scene1.data.link.tate.qOrder i.1 := hSourceOrder i
  let orderCompatibility : TateOrderNormCompatibility T.scene1.data.link :=
    { uniformizerNorm := completionUniformizerNorm p B C hPlaces
      uniformizerNorm_pos := by
        intro w hw
        simp only [completionUniformizerNorm, dite_eq_left hw]
        exact norm_pos_iff.mpr
          (C.uniformizer_isCompletionUniformizer
            (completionIndex p B hPlaces w hw)).ne_zero
      uniformizerNorm_lt_one := by
        intro w hw
        simp only [completionUniformizerNorm, dite_eq_left hw]
        exact (C.uniformizer_isCompletionUniformizer
          (completionIndex p B hPlaces w hw)).norm_lt_one
      norm_eq_pow_order := by
        intro w hw
        let i := completionIndex p B hPlaces w hw
        have hParameterAt : B.tateParameter i =
            T.scene1.data.link.tate.parameter w := by
          convert hParameter i using 1 <;> rfl
        have hOrderAt : C.orderedQOrder i =
            T.scene1.data.link.tate.qOrder w := by
          simpa [i, completionIndex] using hOrder i
        have hQOrderAt : B.qOrder i =
            T.scene1.data.link.tate.qOrder w := by
          rw [C.completionQOrder_eq_orderNat i]
          exact hOrderAt
        have hwTate : w ∈ T.scene1.data.link.tate.places := by
          rw [← hCompat.places_eq]
          exact hw
        have hNorm : T.scene1.data.link.tate.norm w = ‖B.tateParameter i‖ := by
          calc
            T.scene1.data.link.tate.norm w =
                ‖T.scene1.data.link.tate.parameter w‖ := hTate.norm_eq w hwTate
            _ = ‖B.tateParameter i‖ := congrArg norm hParameterAt.symm
        calc
          T.scene1.data.link.tate.norm w = ‖B.tateParameter i‖ := hNorm
          _ = ‖C.uniformizer i‖ ^ B.qOrder i :=
            C.norm_eq_pow_order i
          _ = completionUniformizerNorm p B C hPlaces w ^
                T.scene1.data.link.tate.qOrder w := by
                  dsimp [completionUniformizerNorm]
                  rw [dite_eq_left hw, hQOrderAt]
                  }
  refine
    { badPlacesOver := B.badPlaces
      badPlacesOver_finite := B.badPlaces_finite
      tateParameter := T.scene1.data.link.tate.parameter
      tateParameter_ne_zero := ?_
      qOrder_coprime := ?_
      badFinset := B.badFinset
      badFinset_spec := B.badFinset_spec
      badPlacesOver_eq_link := hPlaces
      tateParameter_eq_link := fun _ _ => rfl
      orderCompatibility := orderCompatibility
      uniformizer := fun w hw =>
        C.uniformizer (completionIndex p B hPlaces w
          (linkMemOfBad p B hPlaces w hw))
      uniformizer_isCompletionUniformizer := fun w hw =>
        C.uniformizer_isCompletionUniformizer (completionIndex p B hPlaces w
          (linkMemOfBad p B hPlaces w hw))
      uniformizerNorm_eq_chosenNorm := ?_ }
  · intro w hw
    have hwTate : w ∈ T.scene1.data.link.tate.places := by
      rw [← hCompat.places_eq]
      exact linkMemOfBad p B hPlaces w hw
    exact hTate.parameter_nonzero w hwTate
  · intro w hw
    let i := completionIndex p B hPlaces w (linkMemOfBad p B hPlaces w hw)
    have hOrderAt : C.orderedQOrder i =
        T.scene1.data.link.tate.qOrder w := by
      simpa [i, completionIndex, linkMemOfBad] using hOrder i
    have hQOrderAt : B.qOrder i = T.scene1.data.link.tate.qOrder w := by
      rw [C.completionQOrder_eq_orderNat i]
      exact hOrderAt
    change Nat.Coprime T.ell (T.scene1.data.link.tate.qOrder w)
    rw [← hQOrderAt]
    exact C.qOrder_coprime i
  · intro w hw
    have hwLink := linkMemOfBad p B hPlaces w hw
    change completionUniformizerNorm p B C hPlaces w =
      ‖C.uniformizer (completionIndex p B hPlaces w hwLink)‖
    simp [completionUniformizerNorm, hwLink]

end IutQPilotSource

end JoshiTeich.Act1Scene1
