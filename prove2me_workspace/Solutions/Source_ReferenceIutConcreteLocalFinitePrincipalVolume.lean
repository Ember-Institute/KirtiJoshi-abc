import Solutions.Source_ReferenceIutConcreteLocalFinitePrincipalOrbit
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationLogVolume

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open MeasureTheory NumberField
open scoped BigOperators ENNReal Pointwise

universe u

noncomputable section

private theorem haar_toReal_div_image {E G : Type*}
    [MeasurableSpace E] [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : E ≃ᵐ G) (μ : Measure E) (ν : Measure G) [hνHaar : ν.IsAddHaarMeasure]
    (hmap : (μ.map e).IsAddHaarMeasure) (S O : Set E) (I : Set G)
    (hO : μ O = 1) (hI : e '' O = I) (hpos : (ν I).toReal ≠ 0) :
    (ν (e '' S)).toReal / (ν I).toReal = (μ S).toReal := by
  let t := Measure.addHaarScalarFactor ν (μ.map e)
  have hν : ν = t • μ.map e := Measure.isAddLeftInvariant_eq_smul ν (μ.map e)
  have himage (U : Set E) : ν (e '' U) = (t : ℝ≥0∞) * μ U := by
    rw [hν, Measure.smul_apply, MeasurableEquiv.map_apply, e.injective.preimage_image,
      ENNReal.smul_def, smul_eq_mul]
  have hνI : ν I = (t : ℝ≥0∞) := by rw [← hI, himage, hO, mul_one]
  have ht : (t : ℝ) ≠ 0 := by simpa only [hνI, ENNReal.coe_toReal] using hpos
  simpa only [himage S, hνI, ENNReal.toReal_mul, ENNReal.coe_toReal] using
    (mul_div_cancel_left₀ (μ S).toReal ht)

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)
variable (hc : ∀ i, IsOver K p (c i))

private def genuineTensorMeasurableEquiv :
    (genuinePacket p c hc).Tensor ≃ᵐ Tensor K (.finite p) c :=
  (genuineTensorContinuousLinearEquiv p c hc).toHomeomorph.toMeasurableEquiv

private theorem genuineTensorMeasurableEquiv_coe :
    (genuineTensorMeasurableEquiv p c hc :
      (genuinePacket p c hc).Tensor → Tensor K (.finite p) c) = genuineTensorEquiv p c hc :=
  rfl

private theorem genuineTensorMeasurableEquiv_image_normalization :
    genuineTensorMeasurableEquiv p c hc '' ↑((genuinePacket p c hc).normalization) =
      integral p c := by
  rw [genuineTensorMeasurableEquiv_coe p c hc, genuineTensorEquiv_image_normalization p c hc]

private theorem genuineTensorMeasurableEquiv_map_normalizationHaar :
    ((genuinePacket p c hc).normalizationHaar.map
      (genuineTensorMeasurableEquiv p c hc)).IsAddHaarMeasure := by
  let e := genuineTensorContinuousLinearEquiv p c hc
  let μ := (genuinePacket p c hc).normalizationHaar
  change (μ.map e).IsAddHaarMeasure
  exact e.isAddHaarMeasure_map μ

private theorem finiteHaar_toReal_div_genuineTensorEquiv_image
    (S : Set (genuinePacket p c hc).Tensor) :
    (finiteHaar p c (genuineTensorEquiv p c hc '' S)).toReal /
      (finiteHaar p c (integral p c)).toReal =
        ((genuinePacket p c hc).normalizationHaar S).toReal := by
  have hpos : (finiteHaar p c (integral p c)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (finiteHaar_integral_pos p c).ne'
      (finiteHaar_integral_lt_top p c).ne).ne'
  rw [← genuineTensorMeasurableEquiv_coe p c hc]
  exact haar_toReal_div_image (genuineTensorMeasurableEquiv p c hc)
    (genuinePacket p c hc).normalizationHaar (finiteHaar p c)
    (hνHaar := finiteHaar_isAddHaarMeasure p c)
    (genuineTensorMeasurableEquiv_map_normalizationHaar p c hc)
    S ↑((genuinePacket p c hc).normalization) (integral p c)
    (genuinePacket p c hc).normalizationHaar_normalization
    (genuineTensorMeasurableEquiv_image_normalization p c hc) hpos

private theorem finrank_genuineTensorEquiv :
    Module.finrank ℚ_[p] (Tensor K (.finite p) c) =
      Module.finrank ℚ_[p] (genuinePacket p c hc).Tensor :=
  (genuineTensorEquiv p c hc).toLinearEquiv.finrank_eq.symm

private theorem finiteComponentVol_genuineTensorEquiv_image
    (S : Set (genuinePacket p c hc).Tensor) :
    finiteComponentVol p c (genuineTensorEquiv p c hc '' S) =
      (genuinePacket p c hc).normalizationLogVolume S := by
  unfold finiteComponentVol JoshiTeich.Act1Scene1.LocalCompletion.Packet.normalizationLogVolume
  exact congrArg₂ (fun (mass : ℝ) (degree : ℕ) => Real.log mass / (degree : ℝ))
    (finiteHaar_toReal_div_genuineTensorEquiv_image p c hc S)
    (finrank_genuineTensorEquiv p c hc)

include hc in
/-- The finite component's degree-normalized log-volume for scaling one tensor factor. -/
theorem finiteComponentVol_incl_smul_integral (j : ι) (w : FinitePlace K)
    (h : c j = Place.finite w) (x : completionAt K w) (hx : x ≠ 0) :
    finiteComponentVol p c (incl p c j w h x • integral p c) =
      Real.log ‖x‖ / localDeg K w := by
  classical
  let P := genuinePacket p c hc
  let z : ∀ i, P.Factor i := Pi.mulSingle j (completionCongr (eq_finPart h) x)
  have hz_dist : z j = completionCongr (eq_finPart h) x :=
    Pi.mulSingle_eq_same (M := fun k => P.Factor k) j _
  have hz_other (i : ι) (hi : i ≠ j) : z i = 1 :=
    Pi.mulSingle_eq_of_ne (M := fun k => P.Factor k) hi _
  have hz (i : ι) : z i ≠ 0 := by
    by_cases hi : i = j
    · subst i
      rw [hz_dist]
      exact (map_ne_zero_iff (completionCongr (eq_finPart h))
        (completionCongr (eq_finPart h)).injective).mpr hx
    · rw [hz_other i hi]
      exact one_ne_zero
  have hregion :
      genuineTensorEquiv p c hc '' P.principalRegion (P.pure z) =
        incl p c j w h x • integral p c := by
    calc
      _ = genuineTensorEquiv p c hc (P.pure z) • integral p c :=
        genuineTensorEquiv_image_principalRegion p c hc (P.pure z)
      _ = _ := congrArg (· • integral p c) (genuineTensorEquiv_pure_mulSingle p c hc j w h x)
  rw [← hregion, finiteComponentVol_genuineTensorEquiv_image p c hc,
    P.normalizationLogVolume_pure_principalRegion z hz]
  let f (i : ι) : ℝ := Real.log ‖z i‖ / JoshiTeich.Prologue.Arithmetic.localDeg (P.place i)
  change (∑ i, f i) = _
  have hsum : (∑ i, f i) = f j :=
    Finset.sum_eq_single j (fun i _ hi => by simp [f, hz_other i hi])
      (fun hj => (hj (Finset.mem_univ j)).elim)
  have hnorm : ‖z j‖ = ‖x‖ :=
    (congrArg (fun y : P.Factor j => ‖y‖) hz_dist).trans
      (norm_completionCongr (eq_finPart h) x)
  have hdegree : JoshiTeich.Prologue.Arithmetic.localDeg (P.place j) = localDeg K w :=
    congrArg (localDeg K) (eq_finPart h).symm
  calc
    (∑ i, f i) = f j := hsum
    _ = _ := by
      dsimp only [f]
      rw [hnorm, hdegree]

end

end AbcAdaptation.Reference.Iut.LocalConstruct
