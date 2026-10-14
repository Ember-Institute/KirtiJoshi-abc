import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-SUBPROBABILITY-BOUND
source: actual canonical q-pilot bridge and the representative fibre-mass bound.
fidelity: transports the actual strict representative gap to the canonical
degree-one Scene1 q-pilot bundle.  The usable accounting is a subprobability
bound (`fiber mass ≤ 1`), while the mass-one certificate was ruled out in S1.345.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem canonicalScene1AbsLogQ_lt_selectedPaperSum
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
    (C.qPilot p).absLogQ p < iutInitialThetaSelectedQRootPaperSum D := by
  let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink hDegree
  have hRef : (C.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
    simpa [C] using
      Corollary312Scene1QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
        p D base hEll hLink hDegree
  exact hRef.trans_lt (iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum D)

end
end JoshiTeich.Act1Scene1
