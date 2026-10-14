import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap

/-!
source-id: JT-SCENE1-INITIAL-THETA-PAPER-REPRESENTATIVE-NONEXISTENCE
source: actual representative ramification gap and the paper representative
accounting certificate used by `cor:cor312`.
fidelity: proves that the current mass-one representative certificate cannot
coexist with the canonical actual q-pilot source.  The contradiction is
`reference absLogQ < selected paper sum` versus the certificate's equality.
This is negative evidence about the current certificate shape; it does not
construct paper representatives or identify H^1_e/BK.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u
noncomputable section

theorem canonicalPaperRepresentativeAccounting_impossible
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
    (hDegree : Module.finrank ℚ D₀.F = 1)
    (A : Corollary312QPilotPaperRepresentativeAccounting p
      base.target (Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
        p D₀ base hEll hLink hDegree |>.qPilot p))
    [Fintype A.representative]
    (theta : ThetaPilotData ↥D₀.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D₀.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D₀.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D₀ p A theta
      thetaBase packetHull heightData ramification logVolume processionLength) :
    False := by
  let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
    p D₀ base hEll hLink hDegree
  have hReference : (C.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D₀) := by
    simpa [C] using
      Corollary312Scene1QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
        p D₀ base hEll hLink hDegree
  have hAccounting :=
    Corollary312Scene1QPilotData.reference_absLogQ_eq_selectedQRootPaperQLogSum
      p D₀ C hReference A theta thetaBase packetHull heightData ramification
        logVolume processionLength B
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D₀).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D₀}
  letI : Fintype S :=
    (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D₀).fintype
  have hPaper :
      (∑ s : S,
        ((Arithmetic.ramIdx s.1.1 : ℝ) *
          Arithmetic.ordp s.1.1
            ((iutInitialThetaOddSupportTorsionQRootSource D₀).qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1)) =
      iutInitialThetaSelectedQRootPaperSum D₀ := by
    simpa [S, iutInitialThetaSelectedQRootPaperSum] using hAccounting
  have hStrict := iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum D₀
  rw [← hPaper] at hStrict
  linarith

end
end JoshiTeich.Act1Scene1
