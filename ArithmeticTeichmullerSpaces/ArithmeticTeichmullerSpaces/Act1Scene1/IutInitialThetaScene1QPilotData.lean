import ArithmeticTeichmullerSpaces.Act1Scene1.AdelicThetaLinkBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalQPilot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQPilotReferenceBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeSelectedQRootBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotNormalizationAudit
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotDegreeAccountingBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-SCENE1-QPILOT-DATA
source: the actual `InitialThetaData.prime` and its canonical
`AdelicThetaLinkData.ofInitialThetaData`; target-side packet, hull, volume,
and q-family accounting remain the explicit `Corollary312Scene1Data` input.
fidelity: assembles the real q-pilot source into the public Scene1 q-pilot
bundle when the normalization audit's degree-one condition is supplied.
boundary: Scene1/Derived

This adapter keeps the target-side analytic accounting visible.  It only
constructs the source and its weighted normalization from `InitialThetaData`;
it does not infer the target volume, packet/hull accounting, or the equality
between an independently supplied link and the canonical link.
-/

namespace Corollary312Scene1QPilotData

/-!
The target-side Scene1 data already contains the theta and packet carriers
stored in its link.  When that link is the canonical link of the same
`InitialThetaData`, the q-pilot source is therefore derived from the actual
IUT admissible prime rather than supplied as an unrelated structure.
The explicit degree-one hypothesis is exactly the boundary identified by the
raw/weighted normalization audit.
-/
noncomputable def ofCanonicalInitialThetaLink
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hLink : base.target.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D
        base.target.scene1.data.link.theta
        base.target.scene1.data.link.thetaBase
        base.target.scene1.data.link.packetHull
        base.target.scene1.data.link.heightData
        base.target.scene1.data.link.ramification
        base.target.scene1.data.link.logVolume
        base.target.scene1.data.link.processionLength)
    (hDegree : Module.finrank ℚ D.F = 1) :
    Corollary312Scene1QPilotData (K := D.F) (O := O) p := by
  let theta := base.target.scene1.data.link.theta
  let thetaBase := base.target.scene1.data.link.thetaBase
  let packetHull := base.target.scene1.data.link.packetHull
  let heightData := base.target.scene1.data.link.heightData
  let ramification := base.target.scene1.data.link.ramification
  let logVolume := base.target.scene1.data.link.logVolume
  let processionLength := base.target.scene1.data.link.processionLength
  let source := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
    packetHull heightData ramification logVolume processionLength hEll hLink
  have hCompat : QNormTateCompatibility base.target.scene1.data.link :=
    base.qFamily.compatibility
  have hRaw := source.toSceneQPilot_rawQNormDegreeNormalization p hCompat
  refine
    { base := base
      source := source
      sourceNormalization := ?_ }
  exact
    Corollary312QPilotNormalizationAudit.weighted_normalization_of_raw_normalization_of_finrank_eq_one
      p (source.toSceneQPilot p hCompat) source.orderCompatibility hRaw hDegree

theorem cor312_of_canonicalInitialThetaLink_of_degree_one
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hLink : base.target.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D
        base.target.scene1.data.link.theta
        base.target.scene1.data.link.thetaBase
        base.target.scene1.data.link.packetHull
        base.target.scene1.data.link.heightData
        base.target.scene1.data.link.ramification
        base.target.scene1.data.link.logVolume
        base.target.scene1.data.link.processionLength)
    (hDegree : Module.finrank ℚ D.F = 1) :
    Corollary312 p base.target := by
  exact cor312_of_scene1_qPilot_data p
    (ofCanonicalInitialThetaLink p D base hEll hLink hDegree)

/-! The named raw normalization projection also makes the degree-normalized
source finite sum directly consumable from the Scene1 bundle. -/
theorem absLogQ_eq_degreeNormalizedSourceQLogSum
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : Corollary312Scene1QPilotData (K := K) (O := O) p) :
    (D.qPilot p).absLogQ p =
      Corollary312DegreeNormalizedSourceQLogSum p D.base.target
        D.base.qFamily.grouping := by
  exact Corollary312QPilotSourceIndexBridge.absLogQ_eq_degreeNormalizedSourceQLogSum
    p D.source.orderCompatibility (D.rawNormalization p) D.base.ell_prime.pos
    (D.sourceIndexBridge p)

theorem absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hLink : base.target.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D
        base.target.scene1.data.link.theta
        base.target.scene1.data.link.thetaBase
        base.target.scene1.data.link.packetHull
        base.target.scene1.data.link.heightData
        base.target.scene1.data.link.ramification
        base.target.scene1.data.link.logVolume
        base.target.scene1.data.link.processionLength)
    (hDegree : Module.finrank ℚ D.F = 1) :
    let B := ofCanonicalInitialThetaLink p D base hEll hLink hDegree
    (B.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  let hCompat : QNormTateCompatibility base.target.scene1.data.link :=
    base.qFamily.compatibility
  let theta := base.target.scene1.data.link.theta
  let thetaBase := base.target.scene1.data.link.thetaBase
  let packetHull := base.target.scene1.data.link.packetHull
  let heightData := base.target.scene1.data.link.heightData
  let ramification := base.target.scene1.data.link.ramification
  let logVolume := base.target.scene1.data.link.logVolume
  let processionLength := base.target.scene1.data.link.processionLength
  change
    Corollary312QPilotData.absLogQ p
      ((IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase packetHull
        heightData ramification logVolume processionLength hEll hLink).toSceneQPilot
          p hCompat) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D)
  exact Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
    p D theta thetaBase packetHull heightData ramification logVolume processionLength hEll hLink

theorem reference_absLogQ_eq_selectedQRootPaperQLogSum
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D₀ : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (D : Corollary312Scene1QPilotData (K := D₀.F) (O := O) p)
    (hReference :
      (D.qPilot p).absLogQ p =
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D₀))
    (A : Corollary312QPilotPaperRepresentativeAccounting p D.base.target
      (D.qPilot p))
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D₀.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D₀.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D₀.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D₀ p A theta
      thetaBase packetHull heightData ramification logVolume processionLength) :
    let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D₀).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D₀}
    letI : Fintype S :=
      (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D₀).fintype
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D₀) =
      ∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D₀).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1) := by
  have hPaper :=
    Corollary312Scene1QPilotData.absLogQ_eq_selectedQRootPaperQLogSum
      p D₀ D A theta thetaBase packetHull heightData ramification logVolume
      processionLength B
  exact hReference.symm.trans hPaper

end Corollary312Scene1QPilotData

/-!
The raw and degree-normalized q-pilot presentations have different source
normalization contracts over a general number field.  This parallel bundle
keeps the degree-normalized candidate explicit: it carries the actual IUT
source and only the raw norm certificate needed by the degree-normalized
finite-sum bridge.  It does not assert that this candidate is the frozen raw
`Corollary312Scene1QPilotData` target.
-/
structure Corollary312Scene1DegreeNormalizedQPilotData
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  base : Corollary312Scene1Data (K := K) (O := O) p
  source : IutQPilotSource p base.target
  rawNormalization :
    Corollary312RawQNormDegreeNormalization p base.target
      source.orderCompatibility
      (source.toSceneQPilot p base.qFamily.compatibility)

namespace Corollary312Scene1DegreeNormalizedQPilotData

noncomputable def qPilot
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    Corollary312QPilotData p D.base.target :=
  D.source.toSceneQPilot p D.base.qFamily.compatibility

noncomputable def sourceIndexBridge
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    Corollary312QPilotSourceIndexBridge p D.base.target D.base.volume
      (D.qPilot p) D.base.qFamily :=
  Corollary312QPilotSourceIndexBridge.ofGrouping p D.base.target D.base.volume
    (D.qPilot p) D.base.qFamily

theorem absLogQ_eq_degreeNormalizedSourceQLogSum
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := K) (O := O) p) :
    (D.qPilot p).absLogQ p =
      Corollary312DegreeNormalizedSourceQLogSum p D.base.target
        D.base.qFamily.grouping := by
  exact Corollary312QPilotSourceIndexBridge.absLogQ_eq_degreeNormalizedSourceQLogSum
    p D.source.orderCompatibility D.rawNormalization
    D.base.ell_prime.pos (D.sourceIndexBridge p)

end Corollary312Scene1DegreeNormalizedQPilotData

namespace Corollary312Scene1DegreeNormalizedQPilotData

noncomputable def ofCanonicalInitialThetaLink
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hLink : base.target.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D
        base.target.scene1.data.link.theta
        base.target.scene1.data.link.thetaBase
        base.target.scene1.data.link.packetHull
        base.target.scene1.data.link.heightData
        base.target.scene1.data.link.ramification
        base.target.scene1.data.link.logVolume
        base.target.scene1.data.link.processionLength) :
    Corollary312Scene1DegreeNormalizedQPilotData (K := D.F) (O := O) p := by
  let theta := base.target.scene1.data.link.theta
  let thetaBase := base.target.scene1.data.link.thetaBase
  let packetHull := base.target.scene1.data.link.packetHull
  let heightData := base.target.scene1.data.link.heightData
  let ramification := base.target.scene1.data.link.ramification
  let logVolume := base.target.scene1.data.link.logVolume
  let processionLength := base.target.scene1.data.link.processionLength
  let source := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
    packetHull heightData ramification logVolume processionLength hEll hLink
  have hCompat : QNormTateCompatibility base.target.scene1.data.link :=
    base.qFamily.compatibility
  refine
    { base := base
      source := source
      rawNormalization := ?_ }
  exact source.toSceneQPilot_rawQNormDegreeNormalization p hCompat

end Corollary312Scene1DegreeNormalizedQPilotData

end

end JoshiTeich.Act1Scene1
