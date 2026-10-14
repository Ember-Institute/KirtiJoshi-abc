import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalVBadCoefficientAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadHullLogCost

/-!
source-id: JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-COST-BRIDGE
source: canonical q-pilot/reference equality and the actual VBad generated-hull
negative-log cost identity.
fidelity: identifies the canonical degree-one Scene1 q-pilot with the
per-procession cost of the actual ordinary-log VBad generated hull.  It does
not identify that hull with Core `thetaVolume` or a Bloch--Kato/theta object.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u
noncomputable section

theorem canonicalScene1AbsLogQ_eq_vbadGeneratedCost_div
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
    (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
      p D base hEll hLink hDegree
    (C.qPilot p).absLogQ p =
      VBadThetaHullLogCost.cost D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ) / (n : ℝ) := by
  let C := Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink hDegree
  have hRef : (C.qPilot p).absLogQ p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
    simpa [C] using
      Corollary312Scene1QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink
        p D base hEll hLink hDegree
  change (C.qPilot p).absLogQ p = _
  rw [hRef, VBadThetaHullLogCost.ordinary_cost_eq_mul_referenceAbsLogQ D n σ hσ]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end
end JoshiTeich.Act1Scene1
