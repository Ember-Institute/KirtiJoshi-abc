import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLinkSource
import ArithmeticTeichmullerSpaces.Act1Scene1.FieldOrientationAudit

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-FIELD-ORIENTATION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`, and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean`.
fidelity: builds the torsion-field Tate-parameter carrier from the actual
`InitialThetaData` Tate family and proves that its local parameter is the
completion image exported by the actual q-root source. The target Scene1
link equality and the target prime identification remain explicit inputs.
boundary: Scene1/Derived
-/

private noncomputable def iutInitialThetaTorsionQParameter
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace ↥D.prime.torsionField) :
    w.maximalIdeal.adicCompletion ↥D.prime.torsionField := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  exact if hw : w ∈ R.badFinset then
    ((iutInitialThetaTateFamilyOfTorsion D).S w
      (iutInitialThetaOddSupportTateFamily_badPlace_source D ⟨w, hw⟩)).t.q
  else 0

noncomputable def iutInitialThetaTorsionTateParameterData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}
      } {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Theta.TateParameterData ↥D.prime.torsionField := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  exact
    { places := R.badFinset
      parameter := iutInitialThetaTorsionQParameter D
      norm := fun w => ‖iutInitialThetaTorsionQParameter D w‖ }

theorem iutInitialThetaTorsionTateParameterData_parameter_eq_completion
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (iutInitialThetaTorsionTateParameterData D).parameter v.1 =
      (iutInitialThetaOddSupportTorsionQRootSource D).completionMap v
        ((iutInitialThetaOddSupportBaseQPilotSource D).tateParameter
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace v)) := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have hq := iutInitialThetaOddSupportTateFamily_q_eq_baseParameter D v
  have hMap : R.completionMap v (B.tateParameter (R.basePlace v)) =
      iutEmbedCompletion
        (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) v)
        (B.tateParameter (R.basePlace v)) := by
    rfl
  calc
    (iutInitialThetaTorsionTateParameterData D).parameter v.1 =
        (((iutInitialThetaTateFamilyOfTorsion D).S v.1
          (iutInitialThetaOddSupportTateFamily_badPlace_source D v)).t.q :
          v.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) := by
      simp [iutInitialThetaTorsionTateParameterData,
        iutInitialThetaTorsionQParameter, v.2]
    _ = iutEmbedCompletion
        (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) v)
        (B.tateParameter (R.basePlace v)) := hq
    _ = R.completionMap v (B.tateParameter (R.basePlace v)) := hMap.symm

noncomputable def AdelicThetaLinkData.ofInitialThetaTorsionTateFamily
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ) :
    AdelicThetaLinkData ↥D.prime.torsionField :=
  AdelicThetaLinkData.ofTateParameters
    (iutInitialThetaTorsionTateParameterData D) theta thetaBase packetHull
    heightData ramification logVolume processionLength

/-- The actual torsion-field Tate family discharges the carrier and completion
parameter fields of the field-orientation audit for its canonical Scene1 link.
The target prime and link identifications remain explicit. -/
theorem IutFieldOrientationAudit.ofInitialThetaTorsionTateFamily
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data (↥D.prime.torsionField) O p}
    (theta : ThetaPilotData ↥D.prime.torsionField)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (hEll : T.ell = D.prime.ℓ)
    (hLink : T.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaTorsionTateFamily D theta thetaBase
        packetHull heightData ramification logVolume processionLength) :
    ∃ (B : IutBaseQPilotSource D.F T.ell)
      (R : IutTorsionQRootSource D.F (↥D.prime.torsionField) T.ell B),
      IutFieldOrientationAudit p T B R := by
  let B0 := iutInitialThetaOddSupportBaseQPilotSource D
  let R0 := iutInitialThetaOddSupportTorsionQRootSource D
  let B : IutBaseQPilotSource D.F T.ell :=
    { badPlaces := B0.badPlaces
      badFinset := B0.badFinset
      badFinset_spec := B0.badFinset_spec
      weight := B0.weight
      weight_eq_qPilotWeight := B0.weight_eq_qPilotWeight
      tateParameter := B0.tateParameter
      tateParameter_ne_zero := B0.tateParameter_ne_zero
      tateParameter_norm_lt_one := B0.tateParameter_norm_lt_one }
  let R : IutTorsionQRootSource D.F (↥D.prime.torsionField) T.ell B :=
    { badFinset := R0.badFinset
      basePlace := fun v => R0.basePlace ⟨v.1, v.2⟩
      liesOver := fun v => R0.liesOver ⟨v.1, v.2⟩
      qroot := fun v => R0.qroot ⟨v.1, v.2⟩
      qroot_ne_zero := fun v => R0.qroot_ne_zero ⟨v.1, v.2⟩
      completionMap := fun v => R0.completionMap ⟨v.1, v.2⟩
      qroot_pow_eq := fun v => by
        simpa [hEll] using R0.qroot_pow_eq ⟨v.1, v.2⟩ }
  refine ⟨B, R, ?_⟩
  refine ⟨?_, ?_⟩
  · change (iutInitialThetaOddSupportTorsionQRootSource D).badFinset =
      T.scene1.data.link.places
    rw [hLink]
    rfl
  · intro v
    change (iutInitialThetaOddSupportTorsionQRootSource D).completionMap v
        ((iutInitialThetaOddSupportBaseQPilotSource D).tateParameter
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace v)) =
      T.scene1.data.link.tate.parameter v.1
    rw [hLink]
    exact (iutInitialThetaTorsionTateParameterData_parameter_eq_completion D v).symm

end

end JoshiTeich.Act1Scene1
