import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalRepresentativeProductIncompatibility

/-!
source-id: JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-REFERENCE-PRODUCT-INCOMPATIBILITY
source: the generic weighted q-pilot product identity, an explicit reference
`absLogQ` equality, the representative-to-selected actual product identity,
and the strict actual selected/reference gap.
fidelity: removes the degree-one and canonical-link construction from the
incompatibility statement. Any Scene1 q-pilot bundle with the reference
equality and both explicit representative certificates is contradictory.
This is a negative audit result for the certificate interface, not a claim
that every possible paper carrier must use that interface.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

theorem no_representativeSectionLinkAccounting_of_referenceEquality
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
    False := by
  have hProduct :=
    Corollary312QPilotPaperRepresentativeAccounting.weightedPaperNormalizedSourceQFactorProduct_eq_representativePaperNormalizedSourceQFactorProduct
      p A D.source.orderCompatibility (D.rawNormalization p) D.base.ell_prime.pos
  have hSource := weightedPaperNormalizedSourceQFactorProduct_eq_exp_neg_absLogQ
    p D.base.target (D.qPilot p) D.source.orderCompatibility
      (D.rawNormalization p) D.base.ell_prime.pos
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

end
end JoshiTeich.Act1Scene1
