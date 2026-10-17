import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalVBadCostBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaActualHullCostBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-THETAVOLUME-BRIDGE
source: canonical q-pilot/generated-hull cost bridge and the explicit
theta-volume normalization contract.
fidelity: under the explicit actual-hull-volume condition, identifies the
target thetaVolume with the exponential of the canonical q-pilot cost.  The
actual-hull-volume condition remains an input; no paper theta or Bloch--Kato
identity is inferred.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_absLogQ_of_actualHullVolume
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
    (N : Corollary312VolumeNormalization p base.target)
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ)) :
    base.target.thetaVolume =
      Real.exp (-((n : ℝ) *
        ((Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
          p D base hEll hLink hDegree).qPilot p).absLogQ p)) := by
  let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink hDegree
  have hcost := Corollary312VolumeNormalization.cost_eq_actualHull_cost
    (D := D) (n := n) (σ := σ) (hσ := hσ)
    (C := VBadThetaLogCollation.collation D n σ hσ)
    p base.target N hvolume
  have hpilot := canonicalScene1AbsLogQ_eq_vbadGeneratedCost_div
    p D base hEll hLink hDegree n hn σ hσ
  have hcost' : base.target.scene1.data.link.logVolume =
      (n : ℝ) * ((C.qPilot p).absLogQ p) := by
    rw [hcost]
    rw [hpilot]
    field_simp
  rw [N.thetaVolume_eq_exp_neg_logVolume, hcost']

theorem canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_absLogQ_fromScene1Data
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
        ((Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
          p D base hEll hLink hDegree).qPilot p).absLogQ p)) := by
  exact canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_absLogQ_of_actualHullVolume
    p D base hEll hLink hDegree n hn σ hσ base.normalization hvolume

end
end JoshiTeich.Act1Scene1
