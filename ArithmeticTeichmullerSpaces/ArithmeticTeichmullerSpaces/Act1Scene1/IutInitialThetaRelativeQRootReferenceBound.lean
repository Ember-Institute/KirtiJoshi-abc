import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRepresentativeBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-REFERENCE-BOUND
source: actual VBad restriction of full support and the complete relative-root product identity.
fidelity: connects the actual reference and canonical Scene1 q-pilots to the
negative log of the actual normalized relative-root product. Full/VBad equality,
paper volume identity and the theta hull estimate remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

theorem iutInitialThetaReferenceAbsLogQ_le_normalizedRelativeQRootProduct_negLog
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤
      -Real.log (iutInitialThetaNormalizedRelativeQRootProduct D) := by
  rw [iutInitialThetaNormalizedRelativeQRootProduct_negLog_eq_fullBaseSum]
  exact iutInitialThetaReferenceAbsLogQ_le_fullBaseSum D

theorem Corollary312QPilotData.absLogQ_le_normalizedRelativeQRootProduct_negLog_ofCanonicalInitialThetaLink
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p}
    (theta : ThetaPilotData D.F) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData D.F)
    (ramification : Arithmetic.RamificationProfile D.F)
    (logVolume : ℝ) (processionLength : ℕ)
    (hEll : T.ell = D.prime.ℓ)
    (hLink : T.scene1.data.link =
      AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull
        heightData ramification logVolume processionLength) :
    let hCompat : QNormTateCompatibility T.scene1.data.link := by
      rw [hLink]
      exact iutInitialThetaLink_qNormTateCompatibility D theta thetaBase packetHull
        heightData ramification logVolume processionLength
    let S := IutQPilotSource.ofCanonicalInitialThetaLink D p theta thetaBase
      packetHull heightData ramification logVolume processionLength hEll hLink
    (S.toSceneQPilot p hCompat).absLogQ p ≤
      -Real.log (iutInitialThetaNormalizedRelativeQRootProduct D) := by
  have heq :=
    Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
      p D theta thetaBase packetHull heightData ramification logVolume processionLength hEll hLink
  exact heq.trans_le (iutInitialThetaReferenceAbsLogQ_le_normalizedRelativeQRootProduct_negLog D)

end
end JoshiTeich.Act1Scene1
