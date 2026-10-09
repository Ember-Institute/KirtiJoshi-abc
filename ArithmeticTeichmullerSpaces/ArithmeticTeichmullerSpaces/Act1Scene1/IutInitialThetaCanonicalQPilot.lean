import ArithmeticTeichmullerSpaces.Act1Scene1.IutAdmissiblePrimeSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLinkSource

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open TateCurvesTheta
open scoped NumberField

universe u

private lemma tateParameter_eq_of_q_eq
    {K : Type u} [NormedField K] {t₁ t₂ : TateParameter K}
    (h : (t₁.q : K) = (t₂.q : K)) : t₁ = t₂ := by
  cases t₁
  cases t₂
  simp only [TateParameter.mk.injEq]
  exact Units.ext h

/-!
source-id: IUT-COR312-CANONICAL-INITIAL-THETA-QPILOT
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`InitialThetaData.prime`; `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`tate`, `unif`, `unif_isUniformizer`, `q_order_coprime`, and `qOrder`;
JoshiTeich III, `ss:theta-data-fixing2` and `pr:admissible-lifts-tate-params`.
fidelity: specializes the real admissible-prime q-pilot constructor to the
canonical link assembled from the same `InitialThetaData`. It derives the
place carrier, Tate `j` identity, and q-norm/Tate compatibility from that
link. It does not construct theta/packet/volume accounting or identify this
link with an independently supplied paper-side link.
boundary: Scene1/Derived
-/

/-- Build the real q-pilot source when the target uses the canonical link
assembled from the same `InitialThetaData`. The independent theta and packet
data remain explicit inputs to that link. -/
noncomputable def IutQPilotSource.ofCanonicalInitialThetaLink
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (hEll : T.ell = D.prime.ℓ)
    (hLink : T.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength) :
    IutQPilotSource p T := by
  have hCanonicalParameter : ∀ w,
      T.scene1.data.link.tate.parameter w =
        (iutInitialThetaTateParameterData D).parameter w := by
    intro w
    have h := congrArg
      (fun L : AdelicThetaLinkData D.F => L.tate.parameter w) hLink
    simpa [AdelicThetaLinkData.ofInitialThetaData,
      AdelicThetaLinkData.ofTateParameters] using h
  have hPlaces : JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace D.F)) := by
    rw [hLink]
    exact iutInitialThetaLink_places_eq_badPlacesOver D theta thetaBase
      packetHull heightData ramification logVolume processionLength
  have hCompat : QNormTateCompatibility T.scene1.data.link := by
    rw [hLink]
    exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase
      packetHull heightData ramification logVolume processionLength
  have hLinkTateJ : ∀ w (hw : w ∈ T.scene1.data.link.tate.places),
      (TateParameter.ofNormLtOne
        (T.scene1.input_laws.tate_parameter.parameter_nonzero w hw)
        (by
          rw [← T.scene1.input_laws.tate_parameter.norm_eq w hw]
          exact T.scene1.input_laws.tate_parameter.norm_lt_one w hw)).tateJ =
        FinitePlace.embedding w.maximalIdeal D.E.j := by
    intro w hw
    have hwCanonical : w ∈ (iutInitialThetaTateParameterData D).places := by
      simpa [AdelicThetaLinkData.ofInitialThetaData,
        AdelicThetaLinkData.ofTateParameters, hLink] using hw
    let tLink := TateParameter.ofNormLtOne
      (T.scene1.input_laws.tate_parameter.parameter_nonzero w hw)
      (by
        rw [← T.scene1.input_laws.tate_parameter.norm_eq w hw]
        exact T.scene1.input_laws.tate_parameter.norm_lt_one w hw)
    have hq : (tLink.q : w.maximalIdeal.adicCompletion D.F) =
        ((TateParameter.ofNormLtOne
          ((iutInitialThetaTateParameterData_laws D).parameter_nonzero w hwCanonical)
          ((iutInitialThetaTateParameterData_laws D).norm_lt_one w hwCanonical)).q :
            w.maximalIdeal.adicCompletion D.F) := by
      change T.scene1.data.link.tate.parameter w =
        (iutInitialThetaTateParameterData D).parameter w
      exact hCanonicalParameter w
    have hTateEq : tLink =
        TateParameter.ofNormLtOne
          ((iutInitialThetaTateParameterData_laws D).parameter_nonzero w hwCanonical)
          ((iutInitialThetaTateParameterData_laws D).norm_lt_one w hwCanonical) := by
      exact tateParameter_eq_of_q_eq hq
    change tLink.tateJ = _
    calc
      tLink.tateJ =
          (TateParameter.ofNormLtOne
            ((iutInitialThetaTateParameterData_laws D).parameter_nonzero w hwCanonical)
            ((iutInitialThetaTateParameterData_laws D).norm_lt_one w hwCanonical)).tateJ :=
        congrArg TateParameter.tateJ hTateEq
      _ = _ := iutInitialThetaLink_ofNormLtOne_tateParameter_j_eq D w hwCanonical
  exact IutQPilotSource.ofInitialThetaData D p hEll hPlaces hLinkTateJ hCompat

end JoshiTeich.Act1Scene1
