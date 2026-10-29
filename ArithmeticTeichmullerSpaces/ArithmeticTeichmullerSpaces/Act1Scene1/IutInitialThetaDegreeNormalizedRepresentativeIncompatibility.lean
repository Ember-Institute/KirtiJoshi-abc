import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperReferenceProductGap
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeSelectedQRootBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-NORMALIZED-REPRESENTATIVE-INCOMPATIBILITY
source: the degree-normalized actual q-pilot product identity, explicit paper
representative accounting, section-link accounting, and the strict
actual-selected/reference product gap.
fidelity: proves that the current representative certificate interface is also
incompatible with the explicit degree-normalized q-pilot candidate. It does
not construct paper representatives or identify a paper theta locus.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

theorem no_degreeNormalizedRepresentativeSectionLinkAccounting_of_referenceEquality
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D₀ : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (D : Corollary312Scene1DegreeNormalizedQPilotData (K := D₀.F) (O := O) p)
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
    False := by
  have hProduct :=
    Corollary312QPilotPaperRepresentativeAccounting.weightedPaperNormalizedSourceQFactorProduct_eq_representativePaperNormalizedSourceQFactorProduct
      p A D.source.orderCompatibility D.rawNormalization D.base.ell_prime.pos
  have hSource := weightedPaperNormalizedSourceQFactorProduct_eq_exp_neg_absLogQ
    p D.base.target (D.qPilot p) D.source.orderCompatibility
      D.rawNormalization D.base.ell_prime.pos
  have hRep :
      Corollary312QPilotPaperRepresentativeAccounting.representativePaperNormalizedSourceQFactorProduct
        p A =
      Real.exp (-JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D₀)) := by
    calc
      Corollary312QPilotPaperRepresentativeAccounting.representativePaperNormalizedSourceQFactorProduct
          p A = weightedPaperNormalizedSourceQFactorProduct p D.base.target
              (D.qPilot p) := hProduct.symm
      _ = Real.exp (-(D.qPilot p).absLogQ p) := hSource
      _ = Real.exp (-JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D₀)) := by
        rw [hReference]
  have hActual :=
    Corollary312PaperRepresentativeSectionLinkAccounting.representativePaperNormalizedSourceQFactorProduct_eq_actualSelectedPaperRootNormProduct
      p D₀ A theta thetaBase packetHull heightData ramification logVolume processionLength B
  have hGap := actualSelectedPaperRootNormProduct_lt_exp_neg_referenceAbsLogQ D₀
  rw [← hActual, hRep] at hGap
  exact (lt_irrefl _ hGap)

theorem no_canonicalDegreeNormalizedRepresentativeSectionLinkAccounting
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D₀ : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D₀.F) (O := O) p)
    (hEll : base.target.ell = D₀.prime.ℓ)
    (hLink : base.target.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D₀
        base.target.scene1.data.link.theta
        base.target.scene1.data.link.thetaBase
        base.target.scene1.data.link.packetHull
        base.target.scene1.data.link.heightData
        base.target.scene1.data.link.ramification
        base.target.scene1.data.link.logVolume
        base.target.scene1.data.link.processionLength)
    (A : Corollary312QPilotPaperRepresentativeAccounting p base.target
      ((Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
        p D₀ base hEll hLink).qPilot p))
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D₀.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D₀.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D₀.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D₀ p A theta
      thetaBase packetHull heightData ramification logVolume processionLength) :
    False := by
  let C := Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
    p D₀ base hEll hLink
  have hReference : (C.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D₀) := by
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
          ((IutQPilotSource.ofCanonicalInitialThetaLink D₀ p theta thetaBase
            packetHull heightData ramification logVolume processionLength hEll hLink).toSceneQPilot
              p hCompat) =
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D₀)
    exact Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
      p D₀ theta thetaBase packetHull heightData ramification logVolume processionLength hEll hLink
  exact no_degreeNormalizedRepresentativeSectionLinkAccounting_of_referenceEquality
    p D₀ C hReference A theta thetaBase packetHull heightData ramification
      logVolume processionLength B

end
end JoshiTeich.Act1Scene1
