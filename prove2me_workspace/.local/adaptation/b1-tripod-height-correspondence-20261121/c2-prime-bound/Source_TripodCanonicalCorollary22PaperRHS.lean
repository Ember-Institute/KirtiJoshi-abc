import Solutions.Source_ReferenceIutPaperRHSTransport
import Solutions.Source_TripodP7
import Solutions.Source_TripodCanonicalCorollary22PrimeBound

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- At each admissible point and selected prime, supply the paper right-hand side and its
local estimate on the concrete P7 data for that point and prime. -/
def PaperRHSSupplyAtLeast {K : T.CBS} {d : ℕ} (minimum : ℕ)
    (Paper : Corollary312VariantData.{u, v} AG TG → Prop) (I : Corollary22Inputs T K d) : Prop :=
  ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d), x ∉ I.excCore →
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv w) →
    (∀ w ∈ (I.localData x hx).bad, (I.localData x hx).p w = ℓ →
      ((I.localData x hx).hv w : ℝ) < Real.sqrt (I.h x)) →
    (∃ w ∈ (I.localData x hx).bad,
      (I.localData x hx).p w ≠ 2 ∧ (I.localData x hx).p w ≠ ℓ) →
    I.SL2Image x ℓ →
    ∀ (D : InitialThetaData.{u} AG TG) (LT : LocalTheory.{u, v} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D), TowerArithmetic D LT TL →
      let X := concreteVariantData D LT TL QI
      let inv := TL.invariants QI
      X.ℓ = ℓ → minimum ≤ X.ℓ → X.dmod ≤ d →
      X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ →
      T.logDiff T.tripod x = inv.logDtpd →
      inv.logFtpd ≤ T.logCond T.tripod x →
      T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ) →
      ∃ R : RHSData.{u, v} D, Paper (X.withRHSData R) ∧
        Nonempty (inv.withRHSData R).LocalEstimate

/-- Attach the paper right-hand side to the concrete data at the prime supplied by (P7). -/
theorem ConcreteThetaDataExistence.toThetaDataExistenceAtLeast_withRHSData
    {K : T.CBS} {d : ℕ} {I : Corollary22Inputs T K d} {minimum : ℕ}
    {Paper : Corollary312VariantData.{u, v} AG TG → Prop}
    (ex : ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) I)
    (supply : PaperRHSSupplyAtLeast minimum Paper I) : ThetaDataExistenceAtLeast minimum Paper I where
  thetaData x hx hxe ℓ hℓp hℓ7 hMinimum hP2 hP3 hP5 hP6 := by
    obtain ⟨D, LT, TL, QI, TA, hPrime, hMod, hQ, hDiff, hCondLower, hCondUpper⟩ :=
      ex x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6
    let X := concreteVariantData D LT TL QI
    let inv := TL.invariants QI
    have hSeven : 7 ≤ D.ℓ := hPrime.symm ▸ hℓ7
    have hDataMinimum : minimum ≤ D.ℓ := hPrime.symm ▸ hMinimum
    obtain ⟨R, hPaper, est⟩ := supply x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6
      D LT TL QI TA hPrime hDataMinimum hMod hQ hDiff hCondLower hCondUpper
    exact exists_p7_witness_withRHSData (X := X) (x := x) (hx := hx) (ℓ := ℓ) (Paper := Paper)
      I R inv (TA.certificate (QI := QI) hSeven) hPaper est
      hPrime hMod hQ hDiff hCondLower hCondUpper

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

variable {AG : AnabelianGeometry.{0}} {TG : TemperedGeometry AG}

/-- The canonical Corollary 2.2 estimate from source P7, a pointwise paper right-hand side,
and the comparison above a prime bound for each compactly bounded family and degree. -/
theorem canonicalCorollary22HighHeightEstimate_of_sourceP7_withPaperRHS
    (P : CurveProviders) {TK : CompactlyBounded → ℝ}
    (CF : ∀ K d, CurveFactsProp P K d (TK K))
    (hcore : ∀ K d, CoreFinitenessHyp P K d AG)
    (anab : AnabelianExistence AG TG) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (minimum : CompactlyBounded → ℕ → ℕ)
    (Paper : CompactlyBounded → ℕ → Corollary312VariantData.{0, 0} AG TG → Prop)
    (supply : ∀ K d, PaperRHSSupplyAtLeast (minimum K d) (Paper K d)
      (curveInputs_from_source P K d (CF K d) (hcore K d) northcottHyp
        (legendreHeight P K) (twoAdicBound P K)).toCorollary22Inputs)
    (h312 : ∀ K d X, Paper K d X → minimum K d ≤ X.ℓ → Corollary312Variant X) :
    CanonicalCorollary22HighHeightEstimate :=
  canonicalCorollary22HighHeightEstimate_of_thetaDataExistenceAtLeast P CF hcore cheb pnt
    minimum Paper (fun K d =>
      ConcreteThetaDataExistence.toThetaDataExistenceAtLeast_withRHSData
        (concreteThetaDataExistence_from_source P K d (CF K d) (hcore K d) northcottHyp anab)
        (supply K d)) h312

end AbcAdaptation.Tripod
