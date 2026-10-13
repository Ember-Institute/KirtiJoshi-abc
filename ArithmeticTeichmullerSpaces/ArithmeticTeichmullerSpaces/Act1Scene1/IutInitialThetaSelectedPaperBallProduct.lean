import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeQRootSum
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarNorm

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-PAPER-BALL-PRODUCT
source: actual torsion q-root equation, normalized local Haar scalar balls,
Joshi III uniformizer normalization at 1748 and 2086, and cor:cor312.
fidelity: constructs actual root balls and corrects their real Haar volumes
by the residue degree. The selected finite product has negative logarithm
equal to the selected paper sum. This corrected product is a numerical
volume normalization, not an additive Haar measure or the final theta hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical Valued

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

theorem iutInitialThetaFullQRoot_norm_lt_one
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ < 1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have hmap : R.completionMap s = iutEmbedCompletion (R.liesOver s) := rfl
  have h := congrArg norm (R.qroot_pow_eq s)
  rw [norm_pow, hmap] at h
  have hm := (iutEmbedCompletion_norm_lt_one_iff (R.liesOver s)
    (B.tateParameter (R.basePlace s))).mpr (B.tateParameter_norm_lt_one (R.basePlace s))
  rw [← h] at hm
  have hn : 2 * D.prime.ℓ ≠ 0 := by have := D.prime.five_le; omega
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn).mp hm

def iutInitialThetaQRootIntegralBall
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Set (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
  (fun x => (iutInitialThetaOddSupportTorsionQRootSource D).qroot s * x) ''
    Metric.closedBall 0 1

theorem iutInitialThetaQRootIntegralBall_haar_toReal_eq_norm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalCompletion.normalizedHaar s.1 (iutInitialThetaQRootIntegralBall D s)).toReal =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let z : LocalCompletion.integerRing s.1 :=
    ⟨R.qroot s, Valued.toNormedField.norm_le_one_iff.mp
      (iutInitialThetaFullQRoot_norm_lt_one D s).le⟩
  have hz : z ≠ 0 := by
    intro h
    exact R.qroot_ne_zero s
      (congrArg (fun x : LocalCompletion.integerRing s.1 =>
        (x : s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField)) h)
  exact LocalCompletion.normalizedHaar_scalarBall_toReal_eq_norm s.1 z hz _
    (Arithmetic.completionQOrder_valued s.1 (R.qroot s) (R.qroot_ne_zero s)
      (iutInitialThetaFullQRoot_norm_lt_one D s))

/-- Residue-degree correction of the actual scalar-ball Haar volume. -/
def iutInitialThetaPaperBallVolume
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : ℝ :=
  (LocalCompletion.normalizedHaar s.1 (iutInitialThetaQRootIntegralBall D s)).toReal ^
    (1 / (Arithmetic.inertDeg s.1 : ℝ))

theorem iutInitialThetaPaperBallVolume_mem_Ioo
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    iutInitialThetaPaperBallVolume D s ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold iutInitialThetaPaperBallVolume
  rw [iutInitialThetaQRootIntegralBall_haar_toReal_eq_norm]
  have hnorm := norm_pos_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)
  have hf : (0 : ℝ) < Arithmetic.inertDeg s.1 := by exact_mod_cast Arithmetic.inertDeg_pos s.1
  exact ⟨Real.rpow_pos_of_pos hnorm _,
    Real.rpow_lt_one hnorm.le (iutInitialThetaFullQRoot_norm_lt_one D s) (div_pos (by norm_num) hf)⟩

theorem iutInitialThetaPaperBallVolume_negLog_eq_paperTerm
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    -Real.log (iutInitialThetaPaperBallVolume D s) =
      ((Arithmetic.ramIdx s.1 : ℝ) * Arithmetic.ordp s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s)) *
          Real.log (Arithmetic.residueChar s.1) := by
  unfold iutInitialThetaPaperBallVolume
  rw [iutInitialThetaQRootIntegralBall_haar_toReal_eq_norm,
    Real.log_rpow (norm_pos_iff.mpr
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s))]
  have hr : (Arithmetic.ramIdx s.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos s.1).ne'
  have hf : (Arithmetic.inertDeg s.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.inertDeg_pos s.1).ne'
  have hp : Real.log (Arithmetic.residueChar s.1) ≠ 0 := ne_of_gt
    (Real.log_pos (by exact_mod_cast (Arithmetic.residueChar_prime s.1).one_lt))
  unfold Arithmetic.ordp Arithmetic.localDeg
  push_cast
  field_simp [hr, hf, hp]
  <;> ring

def iutInitialThetaSelectedPaperBallProduct
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : ℝ :=
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  ∏ s : S, iutInitialThetaPaperBallVolume D s.1

theorem iutInitialThetaSelectedPaperBallProduct_negLog_eq_paperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    -Real.log (iutInitialThetaSelectedPaperBallProduct D) =
      iutInitialThetaSelectedQRootPaperSum D := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  unfold iutInitialThetaSelectedPaperBallProduct
  calc
    _ = -(∑ s : S, Real.log (iutInitialThetaPaperBallVolume D s.1)) := by
      rw [Real.log_prod (fun s _ => ne_of_gt (iutInitialThetaPaperBallVolume_mem_Ioo D s.1).1)]
    _ = ∑ s : S, -Real.log (iutInitialThetaPaperBallVolume D s.1) := by
      rw [Finset.sum_neg_distrib]
    _ = ∑ s : S, ((Arithmetic.ramIdx s.1.1 : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1)) *
        Real.log (Arithmetic.residueChar s.1.1) := by
      exact Finset.sum_congr rfl fun s _ => iutInitialThetaPaperBallVolume_negLog_eq_paperTerm D s.1
    _ = _ := rfl

theorem iutInitialThetaSelectedPaperBallProduct_mem_Ioo
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaSelectedPaperBallProduct D ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos : 0 < iutInitialThetaSelectedPaperBallProduct D := by
    unfold iutInitialThetaSelectedPaperBallProduct
    exact Finset.prod_pos fun s _ => (iutInitialThetaPaperBallVolume_mem_Ioo D s.1).1
  refine ⟨hpos, ?_⟩
  have hlog := iutInitialThetaSelectedPaperBallProduct_negLog_eq_paperSum D
  have hsum := iutInitialThetaSelectedQRootPaperSum_pos D
  exact (Real.log_neg_iff hpos).mp (by linarith)

end
end JoshiTeich.Act1Scene1
