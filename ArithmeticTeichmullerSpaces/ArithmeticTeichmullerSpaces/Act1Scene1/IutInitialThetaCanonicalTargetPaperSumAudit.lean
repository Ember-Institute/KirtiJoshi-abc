import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTateQPilotTargetAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap

/-!
source-id: JT-SCENE1-CANONICAL-TARGET-PAPER-SUM-INCOMPATIBILITY
source: S1.356 target/reference accounting and the actual strict representative
ramification gap of S1.283.
fidelity: proves the canonical degree-one target qLogSum is strictly smaller
than the current selected paper sum. Consequently the additional equality
required by S1.351 and S1.352 is impossible on their canonical source path.
This rules out that assembly path; it does not refute the paper inequality.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem canonicalTateTarget_qLogSum_lt_selectedPaperSum
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D)
    (hDegree : Module.finrank ℚ D.F = 1) :
    Corollary312Data.qLogSum p base.target <
      iutInitialThetaSelectedQRootPaperSum D := by
  rw [Corollary312Scene1QPilotData.qLogSum_eq_reference_ofCanonicalInitialThetaTateData
    p D base hEll hTate hDegree]
  exact iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum D

theorem canonicalTateTarget_selectedPaperAccounting_impossible
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (base : Corollary312Scene1Data (K := D.F) (O := O) p)
    (hEll : base.target.ell = D.prime.ℓ)
    (hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D)
    (hDegree : Module.finrank ℚ D.F = 1)
    (hq : Corollary312Data.qLogSum p base.target =
      iutInitialThetaSelectedQRootPaperSum D) : False := by
  have hlt := canonicalTateTarget_qLogSum_lt_selectedPaperSum
    p D base hEll hTate hDegree
  rw [hq] at hlt
  exact (lt_irrefl _ hlt)

theorem canonicalLinkTarget_selectedPaperAccounting_impossible
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
    (hq : Corollary312Data.qLogSum p base.target =
      iutInitialThetaSelectedQRootPaperSum D) : False := by
  have hTate : base.target.scene1.data.link.tate =
      iutInitialThetaTateParameterData D := congrArg AdelicThetaLinkData.tate hLink
  exact canonicalTateTarget_selectedPaperAccounting_impossible
    p D base hEll hTate hDegree hq

end
end JoshiTeich.Act1Scene1
