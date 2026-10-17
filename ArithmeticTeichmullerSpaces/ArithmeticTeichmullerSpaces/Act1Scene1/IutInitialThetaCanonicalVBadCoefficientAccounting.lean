import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalVBadSubprobabilityBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-COEFFICIENT-ACCOUNTING
source: actual VBad coefficient-weighted paper accounting and the canonical
q-pilot/reference bridge.
fidelity: identifies the canonical degree-one Scene1 q-pilot with the exact
coefficient-weighted sum over the actual VBad selected carrier.  It preserves
the ramification coefficients and does not impose the S1.345 mass-one shape.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem canonicalScene1AbsLogQ_eq_vbadCoefficientWeightedPaperSum
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
    let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
      p D base hEll hLink hDegree
    (C.qPilot p).absLogQ p =
      ∑ v : iutInitialThetaVBadModuliFinset D,
        iutInitialThetaRepresentativeCoefficient D
            (iutInitialThetaVBadModuliAt D v) *
          VBadSelectedPaper.paperTerm D v := by
  let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink hDegree
  have hRef : (C.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
    simpa [C] using
      Corollary312Scene1QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
        p D base hEll hLink hDegree
  exact hRef.trans (VBadSelectedPaper.referenceAbsLogQ_eq_coefficientWeightedPaperSum D)

theorem canonicalScene1AbsLogQ_eq_vbadCoefficientWeightedPaperSum_fromScene1Data
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
    let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
      p D base hEll hLink hDegree
    (C.qPilot p).absLogQ p =
      ∑ v : iutInitialThetaVBadModuliFinset D,
        iutInitialThetaRepresentativeCoefficient D
            (iutInitialThetaVBadModuliAt D v) *
          VBadSelectedPaper.paperTerm D v := by
  exact canonicalScene1AbsLogQ_eq_vbadCoefficientWeightedPaperSum
    p D base hEll hLink hDegree

end
end JoshiTeich.Act1Scene1
