import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadPlaceFiniteness
import ArithmeticTeichmullerSpaces.Act1Scene1.QNormTateBridge
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open TateCurvesTheta
open scoped NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-ADELIC-LINK
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`InitialThetaData.prime`; `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`AdmissiblePrimeData.tate` and `tateJ_eq`; `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`,
`badPlacesOver` and `IsInitialThetaGlobalData.bad_nonempty`.
fidelity: constructs the finite-place and Tate-parameter fields of an
`AdelicThetaLinkData` from actual `InitialThetaData`. The independent theta,
packet/hull, height, ramification, and volume fields remain explicit. This does
not construct `PrologueInputLaws` or identify an independently supplied Scene1
link with this canonical IUT-derived link.
boundary: Scene1/Derived
-/

private def iutInitialThetaQParameter
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F) :
    w.maximalIdeal.adicCompletion D.F := by
  classical
  exact if hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
    (D.prime.tate w hw).q
  else 0

private lemma iutInitialThetaQParameter_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    iutInitialThetaQParameter D w = (D.prime.tate w hw).q := by
  simp [iutInitialThetaQParameter, hw]

private lemma iutTateParameter_eq_of_q_eq
    {K : Type u} [NormedField K] {t₁ t₂ : TateParameter K}
    (h : (t₁.q : K) = (t₂.q : K)) : t₁ = t₂ := by
  cases t₁
  cases t₂
  simp only [TateParameter.mk.injEq]
  exact Units.ext h

/-- The local parameter family read directly from the actual IUT admissible
prime, with its carrier enumerated by the proved finite bad-place set. -/
noncomputable def iutInitialThetaTateParameterData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : Theta.TateParameterData D.F := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  exact
    { places := B.badFinset
      parameter := iutInitialThetaQParameter D
      norm := fun w => ‖iutInitialThetaQParameter D w‖ }

theorem iutInitialThetaTateParameterData_places_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
      (↑(iutInitialThetaTateParameterData D).places :
        Set (NumberField.FinitePlace D.F)) := by
  change JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
    (↑(IutBaseQPilotSource.ofInitialThetaData D).badFinset :
      Set (NumberField.FinitePlace D.F))
  exact (IutBaseQPilotSource.ofInitialThetaData D).badFinset_spec.symm

theorem iutInitialThetaTateParameterData_laws
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Theta.TateParameterLaws (iutInitialThetaTateParameterData D) := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  constructor
  · obtain ⟨v, hv⟩ := D.global.bad_nonempty
    obtain ⟨w, hw⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := D.F) v
    have hbad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := ⟨v, hv, hw⟩
    have hfin : w ∈ B.badFinset := by
      exact (Set.ext_iff.mp B.badFinset_spec w).2 hbad
    exact ⟨w, hfin⟩
  · intro w hw
    change w ∈ B.badFinset at hw
    have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
      exact (Set.ext_iff.mp (iutInitialThetaTateParameterData_places_eq D) w).2
        (Finset.mem_coe.mpr hw)
    change iutInitialThetaQParameter D w ≠ 0
    rw [iutInitialThetaQParameter_eq D w hwBad]
    exact (D.prime.tate w hwBad).q.ne_zero
  · intro w hw
    rfl
  · intro w hw
    change w ∈ B.badFinset at hw
    have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
      exact (Set.ext_iff.mp (iutInitialThetaTateParameterData_places_eq D) w).2
        (Finset.mem_coe.mpr hw)
    change 0 < ‖iutInitialThetaQParameter D w‖
    rw [iutInitialThetaQParameter_eq D w hwBad]
    exact (D.prime.tate w hwBad).norm_q_pos
  · intro w hw
    change w ∈ B.badFinset at hw
    have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
      exact (Set.ext_iff.mp (iutInitialThetaTateParameterData_places_eq D) w).2
        (Finset.mem_coe.mpr hw)
    change ‖iutInitialThetaQParameter D w‖ < 1
    rw [iutInitialThetaQParameter_eq D w hwBad]
    exact (D.prime.tate w hwBad).norm_lt_one

/-- Build the adelic link's finite-place and Tate fields from actual IUT data.
The remaining theta and arithmetic payloads stay caller-supplied. -/
noncomputable def AdelicThetaLinkData.ofInitialThetaData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ) :
    AdelicThetaLinkData D.F :=
  AdelicThetaLinkData.ofTateParameters
    (iutInitialThetaTateParameterData D) theta thetaBase packetHull heightData
    ramification logVolume processionLength

theorem iutInitialThetaLink_places_eq_badPlacesOver
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ) :
    JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
      (↑(AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength).places :
          Set (NumberField.FinitePlace D.F)) := by
  exact iutInitialThetaTateParameterData_places_eq D

theorem iutInitialThetaLink_parameter_eq_prime_tate
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    {w : NumberField.FinitePlace D.F}
    (hw : w ∈ (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength).places)
    (hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
      heightData ramification logVolume processionLength).tate.parameter w =
      (D.prime.tate w hwBad).q := by
  simp [AdelicThetaLinkData.ofInitialThetaData, AdelicThetaLinkData.ofTateParameters,
    iutInitialThetaTateParameterData, iutInitialThetaQParameter_eq D w hwBad]

theorem iutInitialThetaLink_qNormTateCompatibility
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ) :
    QNormTateCompatibility
      (AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength) := by
  exact qNormTateCompatibility_of_tateParameters
    (iutInitialThetaTateParameterData D) theta thetaBase packetHull heightData
    ramification logVolume processionLength

private noncomputable def iutInitialThetaLinkTateParameter
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F)
    (hw : w ∈ (iutInitialThetaTateParameterData D).places) :
    TateParameter (w.maximalIdeal.adicCompletion D.F) :=
  TateParameter.ofNormLtOne
    ((iutInitialThetaTateParameterData_laws D).parameter_nonzero w hw)
    ((iutInitialThetaTateParameterData_laws D).norm_lt_one w hw)

theorem iutInitialThetaLink_tateParameter_j_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F)
    (hw : w ∈ (iutInitialThetaTateParameterData D).places) :
    (iutInitialThetaLinkTateParameter D w hw).tateJ =
      FinitePlace.embedding w.maximalIdeal D.E.j := by
  have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
    rw [iutInitialThetaTateParameterData_places_eq D]
    exact hw
  have hq : (iutInitialThetaTateParameterData D).parameter w =
      (D.prime.tate w hwBad).q :=
    iutInitialThetaQParameter_eq D w hwBad
  have hTate : iutInitialThetaLinkTateParameter D w hw =
      D.prime.tate w hwBad := by
    exact iutTateParameter_eq_of_q_eq hq
  rw [hTate]
  exact D.prime.tateJ_eq w hwBad

theorem iutInitialThetaLink_ofNormLtOne_tateParameter_j_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F)
    (hw : w ∈ (iutInitialThetaTateParameterData D).places) :
    (TateParameter.ofNormLtOne
      ((iutInitialThetaTateParameterData_laws D).parameter_nonzero w hw)
      ((iutInitialThetaTateParameterData_laws D).norm_lt_one w hw)).tateJ =
      FinitePlace.embedding w.maximalIdeal D.E.j := by
  let t₁ := TateParameter.ofNormLtOne
    ((iutInitialThetaTateParameterData_laws D).parameter_nonzero w hw)
    ((iutInitialThetaTateParameterData_laws D).norm_lt_one w hw)
  let t₂ := iutInitialThetaLinkTateParameter D w hw
  have hq : (t₁.q : w.maximalIdeal.adicCompletion D.F) =
      (t₂.q : w.maximalIdeal.adicCompletion D.F) := by
    rfl
  have hEq : t₁ = t₂ := by
    exact iutTateParameter_eq_of_q_eq hq
  rw [show TateParameter.ofNormLtOne
      ((iutInitialThetaTateParameterData_laws D).parameter_nonzero w hw)
      ((iutInitialThetaTateParameterData_laws D).norm_lt_one w hw) = t₁ by rfl,
      hEq]
  exact iutInitialThetaLink_tateParameter_j_eq D w hw

end

end JoshiTeich.Act1Scene1
