import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullReferenceVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTateQPilotTargetAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaActualRawVolumeBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalRawTargetAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.VolumeNormalizationBridge

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-QPRODUCT-EQUALITY
source: the actual-hull/reference theta-volume exponential bridge and the
canonical Tate q-product exponential normalization.
fidelity: under explicit Tate/link, degree-one, procession-length, and
actual-hull-volume conditions, proves equality of the target q-product and
actual thetaVolume. This is an actual conditional consumer; it does not
identify the hull with the paper theta locus or prove the paper volume law.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

theorem canonicalScene1ThetaVolume_eq_qProduct_of_actualHullVolume
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
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ)) :
    base.target.thetaVolume =
      Corollary312Data.qProduct p base.target base.volume.qFactor := by
  have hVolume :=
    canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_referenceAbsLogQ_of_actualHullVolume
      p D base hEll hLink hDegree n hn σ hσ hvolume
  have hQProduct :=
    InitialThetaRawQ.canonicalTateScene1Data_qProduct_eq_exp_neg_ellStar_mul_qLogSum
      p D base base.qFamily
  have hQLog :=
    Corollary312Scene1QPilotData.qLogSum_eq_reference_ofCanonicalInitialThetaTateData
      p D base hEll hTate hDegree
  rw [hQProduct, hlength, hQLog]
  exact hVolume

theorem canonicalTateQProduct_eq_actualHullThetaVolume_pow_finrank_of_normalization
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
    (N : Corollary312VolumeNormalization p base.target)
    (n : ℕ)
    (σ : iutInitialThetaVBadModuliFinset D → Fin n →
      (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
    (hlength : base.target.ellStar = n)
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ)) :
    Corollary312Data.qProduct p base.target base.volume.qFactor =
      base.target.thetaVolume ^ Module.finrank ℚ D.F := by
  have hVolume :=
    actualHullThetaVolume_eq_exp_neg_procession_mul_referenceAbsLogQ_of_normalization
      p D base N n σ hσ hvolume
  have hQProduct :=
    InitialThetaRawQ.canonicalTateScene1Data_qProduct_eq_exp_neg_ellStar_mul_qLogSum
      p D base base.qFamily
  have hQLog :=
    canonicalTateScene1Data_qLogSum_eq_degree_mul_reference p D base hEll hTate
  rw [hQProduct, hlength, hQLog, hVolume]
  have hExp : ∀ x : ℝ, ∀ m : ℕ,
      Real.exp (-((m : ℝ) * x)) ^ (Module.finrank ℚ D.F) =
        Real.exp (-((m : ℝ) * (Module.finrank ℚ D.F : ℝ) * x)) := by
    intro x m
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  symm
  simpa [mul_assoc] using
    (hExp (IutTorsionQRootSource.iutInitialThetaQPilotData D).absLogQ n)

end
end JoshiTeich.Act1Scene1
