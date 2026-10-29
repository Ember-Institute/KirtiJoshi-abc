import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalVBadThetaVolumeBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-REFERENCE-VOLUME
source: the canonical actual-hull theta-volume exponential identity and the
canonical Scene1 q-pilot/reference `absLogQ` equality.
fidelity: rewrites the actual conditional volume formula directly in terms
of the reference q-pilot exponent. The actual-hull-volume condition and all
analytic generator/normalization conditions remain explicit; no paper
thetaVolume or Bloch--Kato identity is inferred.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

theorem canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_referenceAbsLogQ_of_actualHullVolume
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
    (n : ℕ) (hn : 0 < n)
    (σ : iutInitialThetaVBadModuliFinset D → Fin n →
      (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ)) :
    base.target.thetaVolume =
      Real.exp (-((n : ℝ) *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D))) := by
  let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink hDegree
  have hVolume :=
    canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_absLogQ_fromScene1Data
      p D base hEll hLink hDegree n hn σ hσ hvolume
  have hReference :=
    Corollary312Scene1QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
      p D base hEll hLink hDegree
  change base.target.thetaVolume =
      Real.exp (-((n : ℝ) * (C.qPilot p).absLogQ p)) at hVolume
  change (C.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) at hReference
  rw [hReference] at hVolume
  exact hVolume

end
end JoshiTeich.Act1Scene1
