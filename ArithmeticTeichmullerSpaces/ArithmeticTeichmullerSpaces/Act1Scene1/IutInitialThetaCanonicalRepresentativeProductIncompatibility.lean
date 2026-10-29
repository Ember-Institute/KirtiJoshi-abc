import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperReferenceProductGap
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeSelectedQRootBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-REPRESENTATIVE-PRODUCT-INCOMPATIBILITY
source: the canonical Scene1 representative product/reference exponential
identity, the representative-to-selected actual product identity, and the
strict actual selected/reference product gap.
fidelity: proves that the three supplied certificates cannot coexist for a
degree-one canonical InitialTheta link. This is a negative audit result about
the explicit representative certificate; it does not construct or reject an
independent paper `L'` carrier.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

theorem no_canonicalRepresentativeSectionLinkAccounting_of_degree_one
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
    (hDegree : Module.finrank ℚ D.F = 1)
    (A : Corollary312QPilotPaperRepresentativeAccounting p base.target
      ((Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
        p D base hEll hLink hDegree).qPilot p))
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D p A theta
      thetaBase packetHull heightData ramification logVolume processionLength) :
    False := by
  have hRep :=
    Corollary312Scene1QPilotData.representativePaperNormalizedSourceQFactorProduct_eq_exp_neg_referenceAbsLogQ_ofCanonicalInitialThetaLink
      p D base hEll hLink hDegree A
  have hActual :=
    Corollary312PaperRepresentativeSectionLinkAccounting.representativePaperNormalizedSourceQFactorProduct_eq_actualSelectedPaperRootNormProduct
      p D A theta thetaBase packetHull heightData ramification logVolume processionLength B
  have hGap := actualSelectedPaperRootNormProduct_lt_exp_neg_referenceAbsLogQ D
  rw [← hActual, hRep] at hGap
  exact (lt_irrefl _ hGap)

end
end JoshiTeich.Act1Scene1
