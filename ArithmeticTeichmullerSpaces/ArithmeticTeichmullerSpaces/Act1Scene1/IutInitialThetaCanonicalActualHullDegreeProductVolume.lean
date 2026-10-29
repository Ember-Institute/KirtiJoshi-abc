import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullReferenceVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullQProductEquality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaActualRawVolumeBound
import ArithmeticTeichmullerSpaces.Act1Scene1.VolumeNormalizationBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaScene1QPilotData
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQPilotRawAccounting

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
  rw [hVolume, hProduct]
  exact (exp_neg_nat_mul_eq_pow
    (JoshiTeich.ReferenceIut.QPilotData.absLogQ
      (IutTorsionQRootSource.iutInitialThetaQPilotData D)) n)

theorem canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_qLogSum_div_degree_of_actualHullVolume
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
        (Corollary312Data.qLogSum p base.target /
          (Module.finrank ℚ D.F : ℝ)))) := by
  let C := Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink
  have hVolume :=
    canonicalScene1ThetaVolume_eq_degreeNormalizedSourceQFactorProduct_pow_of_actualHullVolume
      p D base hEll hLink hDegree n hn σ hσ hvolume
  have hProduct := C.qFactorProduct_eq_exp_neg_qLogSum_div_degree p
  change base.target.thetaVolume =
    Real.exp (-((n : ℝ) *
      (Corollary312Data.qLogSum p base.target /
        (Module.finrank ℚ D.F : ℝ))))
  change base.target.thetaVolume =
    (degreeNormalizedSourceQFactorProduct p C.base.target (C.qPilot p)) ^ n at hVolume
  rw [hVolume, hProduct]
  exact (exp_neg_nat_mul_eq_pow
    (Corollary312Data.qLogSum p base.target /
      (Module.finrank ℚ D.F : ℝ)) n).symm

theorem canonicalScene1QProduct_eq_degreeNormalizedSourceQFactorProduct_pow_of_actualHullVolume
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
    Corollary312Data.qProduct p base.target base.volume.qFactor =
      (degreeNormalizedSourceQFactorProduct p
        (Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
          p D base hEll hLink).base.target
        ((Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
          p D base hEll hLink).qPilot p)) ^ n := by
  have hTheta := canonicalScene1ThetaVolume_eq_qProduct_of_actualHullVolume
    p D base hEll hTate hLink hDegree n hn σ hσ hlength hvolume
  have hProduct := canonicalScene1ThetaVolume_eq_degreeNormalizedSourceQFactorProduct_pow_of_actualHullVolume
    p D base hEll hLink hDegree n hn σ hσ hvolume
  calc
    Corollary312Data.qProduct p base.target base.volume.qFactor =
        base.target.thetaVolume := hTheta.symm
    _ = (degreeNormalizedSourceQFactorProduct p
        (Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
          p D base hEll hLink).base.target
        ((Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
          p D base hEll hLink).qPilot p)) ^ n := hProduct

theorem canonicalScene1QProduct_negLog_eq_procession_mul_degreeNormalizedSourceQFactorProduct_negLog_of_actualHullVolume
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
    -Real.log (Corollary312Data.qProduct p base.target base.volume.qFactor) =
      (n : ℝ) *
        (-Real.log (degreeNormalizedSourceQFactorProduct p
          (Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
            p D base hEll hLink).base.target
          ((Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
            p D base hEll hLink).qPilot p))) := by
  have hProduct := canonicalScene1QProduct_eq_degreeNormalizedSourceQFactorProduct_pow_of_actualHullVolume
    p D base hEll hTate hLink hDegree n hn σ hσ hlength hvolume
  rw [hProduct, Real.log_pow]
  ring

theorem canonicalScene1DegreeNormalizedSourceQFactorProduct_pow_le_actualHullVolume
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
    (n : ℕ)
    (σ : iutInitialThetaVBadModuliFinset D → Fin n →
      (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    (degreeNormalizedSourceQFactorProduct p
      (Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
        p D base hEll hLink).base.target
      ((Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
        p D base hEll hLink).qPilot p)) ^ n ≤
      VBadThetaLogCollation.volume D n σ hσ := by
  let C := Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
    p D base hEll hLink
  have hProduct := C.qFactorProduct_eq_exp_neg_qLogSum_div_degree p
  have hDegreeReal : (Module.finrank ℚ D.F : ℝ) = 1 := by
    exact_mod_cast hDegree
  have hPower :
      (degreeNormalizedSourceQFactorProduct p C.base.target (C.qPilot p)) ^ n =
        Real.exp (-((n : ℝ) * Corollary312Data.qLogSum p base.target)) := by
    rw [hProduct, hDegreeReal, div_one]
    exact (exp_neg_nat_mul_eq_pow (Corollary312Data.qLogSum p base.target) n).symm
  rw [hPower]
  exact InitialThetaRawQ.canonicalTateScene1Data_exp_neg_procession_mul_qLogSum_le_actualVolume
    p D base hEll hTate n σ hσ

theorem corollary312_of_canonicalDegreeNormalizedProduct_actualHullVolume
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
    (V : Corollary312VolumeData p base.target)
    (Q : Corollary312QFamily p base.target V)
    (N : Corollary312VolumeNormalization p base.target)
    (hlength : base.target.ellStar = n)
    (hQFactor : V.qFactor = base.volume.qFactor)
    (hvolume : base.target.thetaVolume =
      VBadThetaCollatedHull.volume D n σ hσ
        (VBadThetaLogCollation.collation D n σ hσ))
    (hEllPrime : Nat.Prime base.target.ell)
    (hEllGeFive : 5 ≤ base.target.ell)
    (hEllStarEq : base.target.ellStar = (base.target.ell - 1) / 2)
    (hEllStarPos : 0 < base.target.ellStar) :
    Corollary312 p base.target := by
  have hProductBound := canonicalScene1DegreeNormalizedSourceQFactorProduct_pow_le_actualHullVolume
    p D base hEll hTate hLink hDegree n σ hσ
  have hQProduct := canonicalScene1QProduct_eq_degreeNormalizedSourceQFactorProduct_pow_of_actualHullVolume
    p D base hEll hTate hLink hDegree n hn σ hσ hlength hvolume
  have hLower : base.target.thetaVolume ≥ Corollary312Data.qProduct p base.target V.qFactor := by
    calc
      Corollary312Data.qProduct p base.target V.qFactor =
          (degreeNormalizedSourceQFactorProduct p
            (Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
              p D base hEll hLink).base.target
            ((Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink
              p D base hEll hLink).qPilot p)) ^ n := by
        rw [hQFactor]
        exact hQProduct
      _ ≤ VBadThetaLogCollation.volume D n σ hσ := hProductBound
      _ = base.target.thetaVolume := hvolume.symm
  have hLog := logVolume_nonneg_of_scene1 p base.target
  have hThetaVolume := thetaVolume_le_one_of_normalization p N hLog
  exact corollary312_of_q_family_normalized_lower_bound p base.target V Q N
    hEllPrime hEllGeFive hEllStarEq hEllStarPos hLower

end
end JoshiTeich.Act1Scene1
