import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullReferenceVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-DEGREE-PRODUCT-VOLUME
source: the conditional actual-hull theta-volume/reference exponent and the
canonical degree-normalized q-pilot product/reference exponent.
fidelity: identifies the actual conditional hull volume with a natural power
of the actual degree-normalized source product. It does not identify either
carrier with the paper theta locus or paper thetaVolume.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

private theorem exp_neg_nat_mul_eq_pow (x : ℝ) (n : ℕ) :
    Real.exp (-((n : ℝ) * x)) = (Real.exp (-x)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, neg_add, Real.exp_add, ih, pow_succ]

 theorem canonicalScene1ThetaVolume_eq_degreeNormalizedSourceQFactorProduct_pow_of_actualHullVolume
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
    let C := Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
      p D base hEll hLink
    base.target.thetaVolume =
      (degreeNormalizedSourceQFactorProduct p C.base.target (C.qPilot p)) ^ n := by
  let C := Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink
  have hVolume :=
    canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_referenceAbsLogQ_of_actualHullVolume
      p D base hEll hLink hDegree n hn σ hσ hvolume
  have hProduct :=
    Corollary312Scene1DegreeNormalizedQPilotData.qFactorProduct_eq_exp_neg_referenceAbsLogQ_ofCanonicalInitialThetaLink
      p D base hEll hLink
  change base.target.thetaVolume =
    (degreeNormalizedSourceQFactorProduct p C.base.target (C.qPilot p)) ^ n
  change base.target.thetaVolume =
      Real.exp (-((n : ℝ) *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D))) at hVolume
  dsimp at hProduct
  rw [hVolume, hProduct]
  exact (exp_neg_nat_mul_eq_pow
    (JoshiTeich.ReferenceIut.QPilotData.absLogQ
      (IutTorsionQRootSource.iutInitialThetaQPilotData D)) n)

end
end JoshiTeich.Act1Scene1
