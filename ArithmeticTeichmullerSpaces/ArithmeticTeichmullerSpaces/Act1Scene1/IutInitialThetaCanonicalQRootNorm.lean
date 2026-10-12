import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalSourceAudit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQNormalizationBridge

/-!
source-id: JT-SCENE1-CANONICAL-QROOT-NORM-CERTIFICATE
source: actual InitialThetaData/TateFamily q-root construction, S1.239
canonical Tate parameter identity, and S1.237 completion norm power law.
fidelity: connects the actual torsion-completion root to the base link's raw
q-factor. The exponent includes relative ramification and residue degree.
Paper representatives and the final global normalization remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.CanonicalQRootNorm

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data D.F O p}
variable (hTate : T.scene1.data.link.tate = iutInitialThetaTateParameterData D)
variable (hCompat : QNormTateCompatibility T.scene1.data.link)

/-- Contract the actual q-root place to the same finite carrier as the link. -/
def baseIndex
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    Corollary312SourceQIndex p T := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  refine ⟨(R.basePlace v).1, ?_⟩
  have hwBad : (R.basePlace v).1 ∈
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
    B.mem_badPlaces (R.basePlace v)
  rw [hCompat.places_eq, hTate]
  exact (Set.ext_iff.mp (iutInitialThetaTateParameterData_places_eq D)
    (R.basePlace v).1).mp hwBad

private theorem baseParameter_norm_eq_qNorm
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    ‖(IutBaseQPilotSource.ofInitialThetaData D).tateParameter
        ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).basePlace v)‖ =
      T.scene1.data.link.qNorm (baseIndex D p hTate hCompat v).1 := by
  let L := T.scene1.data.link
  let B := IutBaseQPilotSource.ofInitialThetaData D
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  let w := R.basePlace v
  have hParameter : B.tateParameter w = L.tate.parameter w.1 := by
    rw [hTate]
    exact iutCanonicalBaseSource_tateParameter_eq_link D L.theta L.thetaBase
      L.packetHull L.heightData L.ramification L.logVolume L.processionLength w
  change ‖B.tateParameter w‖ = ‖L.qParameter w.1‖
  rw [hParameter, hCompat.parameter_eq w.1
    (baseIndex D p hTate hCompat v).2]

/-- The actual root equation supplies the full completion norm certificate. -/
theorem norm_pow_eq_qNorm_pow
    (hEll : T.ell = D.prime.ℓ)
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ ^ (2 * T.ell) =
      T.scene1.data.link.qNorm (baseIndex D p hTate hCompat v).1 ^
        (relRamIdx v.1 (baseIndex D p hTate hCompat v).1 *
          relInertDeg v.1 (baseIndex D p hTate hCompat v).1) := by
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  have hMap : R.completionMap v = iutEmbedCompletion (R.liesOver v) := rfl
  have hRoot := congrArg norm (R.qroot_pow_eq v)
  rw [norm_pow, hMap, iutEmbedCompletion_norm_eq_pow,
    baseParameter_norm_eq_qNorm D p hTate hCompat v] at hRoot
  simpa only [hEll, baseIndex, iutRelativeRamificationIndex, relRamIdx, R] using hRoot

/-- The same actual root gives the raw local q-factor logarithmic term. -/
theorem negLog_norm_eq_rawFactor_log_mul
    (hEll : T.ell = D.prime.ℓ)
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    -Real.log ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ =
      (relRamIdx v.1 (baseIndex D p hTate hCompat v).1 *
        relInertDeg v.1 (baseIndex D p hTate hCompat v).1 : ℝ) *
        (-Real.log (Corollary312SourceQFactor p T
          (baseIndex D p hTate hCompat v))) := by
  let i := baseIndex D p hTate hCompat v
  have hEllPos : 0 < T.ell := by
    rw [hEll]
    exact D.prime.ℓ_prime.pos
  have hn : (2 * (T.ell : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < T.ell := by exact_mod_cast hEllPos
    positivity
  have hq : 0 < T.scene1.data.link.qNorm i.1 :=
    T.scene1.input_laws.first_axiom.q_norm_positive i.1 i.2
  have hLog := congrArg (fun x : ℝ => -Real.log x)
    (norm_pow_eq_qNorm_pow D p hTate hCompat hEll v)
  rw [Real.log_pow, Real.log_pow] at hLog
  push_cast at hLog
  change -Real.log ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ =
    (relRamIdx v.1 i.1 * relInertDeg v.1 i.1 : ℝ) *
      (-Real.log (T.scene1.data.link.qNorm i.1 ^ (1 / (2 * (T.ell : ℝ)))))
  rw [Real.log_rpow hq]
  apply (mul_left_cancel₀ hn)
  field_simp [hn]
  nlinarith [hLog]

/-- The raw q-factor also determines the actual root norm itself. -/
theorem norm_eq_rawFactor_pow
    (hEll : T.ell = D.prime.ℓ)
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ =
      Corollary312SourceQFactor p T (baseIndex D p hTate hCompat v) ^
        (relRamIdx v.1 (baseIndex D p hTate hCompat v).1 *
          relInertDeg v.1 (baseIndex D p hTate hCompat v).1) := by
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  let i := baseIndex D p hTate hCompat v
  have hq : 0 < T.scene1.data.link.qNorm i.1 :=
    T.scene1.input_laws.first_axiom.q_norm_positive i.1 i.2
  have hFactor : 0 < Corollary312SourceQFactor p T i :=
    Real.rpow_pos_of_pos hq _
  apply Real.log_injOn_pos (norm_pos_iff.mpr (R.qroot_ne_zero v))
    (pow_pos hFactor _)
  rw [Real.log_pow]
  have h := negLog_norm_eq_rawFactor_log_mul D p hTate hCompat hEll v
  push_cast
  nlinarith [h]

/-- Apply the existing paper norm correction to the actual torsion root. -/
def paperRootNorm
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) : ℝ :=
  ‖(IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot v‖ ^
    (1 / (inertDeg v.1 : ℝ))

/-- Relative residue degree cancels only after both local norms receive the
paper correction. Relative ramification remains in the logarithmic term. -/
theorem negLog_paperRootNorm_eq_paperFactor_log_mul
    (hEll : T.ell = D.prime.ℓ)
    (v : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    -Real.log (paperRootNorm D v) =
      (relRamIdx v.1 (baseIndex D p hTate hCompat v).1 : ℝ) *
        (-Real.log (Corollary312PaperNormalizedSourceQFactor p T
          (baseIndex D p hTate hCompat v))) := by
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  let i := baseIndex D p hTate hCompat v
  have hDegree : (inertDeg v.1 : ℝ) =
      (inertDeg i.1 : ℝ) * (relInertDeg v.1 i.1 : ℝ) := by
    exact_mod_cast inertDeg_eq_mul (R.liesOver v)
  have hv : (inertDeg v.1 : ℝ) ≠ 0 := by
    exact_mod_cast (inertDeg_pos v.1).ne'
  have hw : (inertDeg i.1 : ℝ) ≠ 0 := by
    exact_mod_cast (inertDeg_pos i.1).ne'
  have hf : (relInertDeg v.1 i.1 : ℝ) ≠ 0 := by
    intro hf
    rw [hf, mul_zero] at hDegree
    exact hv hDegree
  have hRoot : 0 < ‖R.qroot v‖ := norm_pos_iff.mpr (R.qroot_ne_zero v)
  unfold paperRootNorm
  rw [Real.log_rpow hRoot,
    paperNormalizedSourceQFactor_log_eq_raw_div_residueDegree p T i]
  have hLog := negLog_norm_eq_rawFactor_log_mul D p hTate hCompat hEll v
  rw [show -(1 / (inertDeg v.1 : ℝ) * Real.log ‖R.qroot v‖) =
      (1 / (inertDeg v.1 : ℝ)) * (-Real.log ‖R.qroot v‖) by ring,
    hLog, hDegree]
  field_simp [hw, hf]
  <;> ring

end
end JoshiTeich.Act1Scene1.CanonicalQRootNorm
