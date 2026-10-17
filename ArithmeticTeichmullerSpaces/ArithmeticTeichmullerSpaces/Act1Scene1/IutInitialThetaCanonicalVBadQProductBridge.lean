import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalVBadThetaVolumeBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaActualHullCostBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-QPRODUCT-BRIDGE
source: the canonical thetaVolume exponential bridge and the actual VBad
collated-hull lower-bound consumer.
fidelity: under the explicit actual-hull-volume and q-family accounting
conditions, rewrites the theta-volume lower bound as an inequality for the
canonical q-pilot exponential. No unconditional paper theta identity is
claimed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem canonicalScene1Exp_neg_procession_mul_absLogQ_ge_qProduct_of_actualHullVolume
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
    (V : Corollary312VolumeData p base.target)
    (Q : Corollary312QFamily p base.target V)
    (N : Corollary312VolumeNormalization p base.target)
    (hlength : base.target.ellStar = n)
    (hq : Corollary312Data.qLogSum p base.target =
      iutInitialThetaSelectedQRootPaperSum D)
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ)) :
    Real.exp (-((n : ℝ) *
      ((Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
        p D base hEll hLink hDegree).qPilot p).absLogQ p)) ≥
      Corollary312Data.qProduct p base.target V.qFactor := by
  have hcost := Corollary312VolumeNormalization.cost_eq_actualHull_cost
    (D := D) (n := n) (σ := σ) (hσ := hσ)
    (C := VBadThetaLogCollation.collation D n σ hσ)
    p base.target N hvolume
  have hLower := thetaVolume_lower_bound_of_actualHull_cost
    (D := D) (n := n) (σ := σ) (hσ := hσ)
    (C := VBadThetaLogCollation.collation D n σ hσ)
    (hgen := VBadThetaLogCollation.generator_coverage D n σ hσ)
    (hunit := VBadThetaLogCollation.collation_subset_normalization D n σ hσ)
    p base.target V Q N hlength hcost hq
  have hTheta := canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_absLogQ_of_actualHullVolume
    p D base hEll hLink hDegree n hn σ hσ N hvolume
  rw [← hTheta]
  exact hLower

theorem canonicalScene1Exp_neg_procession_mul_absLogQ_ge_qProduct_fromScene1Data
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
    (hlength : base.target.ellStar = n)
    (hq : Corollary312Data.qLogSum p base.target =
      iutInitialThetaSelectedQRootPaperSum D)
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ)) :
    Real.exp (-((n : ℝ) *
      ((Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
        p D base hEll hLink hDegree).qPilot p).absLogQ p)) ≥
      Corollary312Data.qProduct p base.target base.volume.qFactor := by
  exact canonicalScene1Exp_neg_procession_mul_absLogQ_ge_qProduct_of_actualHullVolume
    p D base hEll hLink hDegree n hn σ hσ base.volume base.qFamily.toQFamily
    base.normalization hlength hq hvolume

end
end JoshiTeich.Act1Scene1
