import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionGaloisDegree
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperRelativeNormBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-GALOIS-QROOT-CHOICE
source: Joshi III `eq:weights`, the actual representation-kernel torsion field,
Galois conjugacy of its places over F, and the actual q-root power equation.
fidelity: derives equal ramification, residue and local degrees for torsion
source places over one F-place. Their raw and residue-corrected q-root norms
are equal, as are their inverse-completion-degree weighted factors over a
common moduli place. No degree equality or norm equality is supplied as input.
boundary: Scene1/Derived; keeps the same F-place, Initial Theta datum and
untilt. Does not construct paper representatives or mixed-moduli transport.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance torsionGalois : IsGalois D.F ↥D.prime.torsionField :=
  IsGalois.of_fixedField_normal_subgroup D.prime.rep.ker

theorem iutInitialThetaTorsionSource_degrees_eq_of_same_basePlace
    (s t : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hbase : (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s =
      (iutInitialThetaOddSupportTorsionQRootSource D).basePlace t) :
    Arithmetic.ramIdx s.1 = Arithmetic.ramIdx t.1 ∧
      Arithmetic.inertDeg s.1 = Arithmetic.inertDeg t.1 ∧
        Arithmetic.localDeg s.1 = Arithmetic.localDeg t.1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  have ht : Ideal.LiesOver t.1.maximalIdeal.asIdeal (R.basePlace s).1.maximalIdeal.asIdeal := by
    rw [hbase]
    exact R.liesOver t
  exact ⟨LocalCompletion.ramIdx_eq_of_galois_liesOver (R.liesOver s) ht,
    LocalCompletion.inertDeg_eq_of_galois_liesOver (R.liesOver s) ht,
    LocalCompletion.localDeg_eq_of_galois_liesOver (R.liesOver s) ht⟩

theorem iutInitialThetaQRoot_norm_eq_of_same_basePlace
    (s t : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hbase : (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s =
      (iutInitialThetaOddSupportTorsionQRootSource D).basePlace t) :
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s‖ =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot t‖ := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  have hdegree := (iutInitialThetaTorsionSource_degrees_eq_of_same_basePlace D s t hbase).2.2
  have hsDegree := Arithmetic.localDeg_eq_mul (R.liesOver s)
  have htDegree := Arithmetic.localDeg_eq_mul (R.liesOver t)
  rw [hbase] at hsDegree
  have hrelative :
      Arithmetic.relRamIdx s.1 (R.basePlace t).1 * Arithmetic.relInertDeg s.1 (R.basePlace t).1 =
      Arithmetic.relRamIdx t.1 (R.basePlace t).1 * Arithmetic.relInertDeg t.1 (R.basePlace t).1 :=
    Nat.eq_of_mul_eq_mul_left (Arithmetic.localDeg_pos (R.basePlace t).1)
      (hsDegree.symm.trans (hdegree.trans htDegree))
  have hs := congrArg norm (R.qroot_pow_eq s)
  have ht := congrArg norm (R.qroot_pow_eq t)
  have hmapS : R.completionMap s = iutEmbedCompletion (R.liesOver s) := rfl
  have hmapT : R.completionMap t = iutEmbedCompletion (R.liesOver t) := rfl
  rw [norm_pow, hmapS, iutEmbedCompletion_norm_eq_pow] at hs
  rw [norm_pow, hmapT, iutEmbedCompletion_norm_eq_pow] at ht
  rw [hbase, hrelative] at hs
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
    (Nat.mul_ne_zero (by decide : 2 ≠ 0) D.prime.ℓ_prime.ne_zero)).mp (hs.trans ht.symm)

theorem actualPaperRootNorm_eq_of_same_basePlace
    (s t : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hbase : (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s =
      (iutInitialThetaOddSupportTorsionQRootSource D).basePlace t) :
    actualPaperRootNorm D s = actualPaperRootNorm D t := by
  unfold actualPaperRootNorm
  rw [iutInitialThetaQRoot_norm_eq_of_same_basePlace D s t hbase,
    (iutInitialThetaTorsionSource_degrees_eq_of_same_basePlace D s t hbase).2.1]

/-- The inverse relative-completion-degree factors, including the residue
correction, are independent of the over-place within one actual F-place. -/
theorem actualPaperWeightedRootFactor_eq_of_same_basePlace
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (s t : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hbase : (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s =
      (iutInitialThetaOddSupportTorsionQRootSource D).basePlace t)
    (hsv : Ideal.LiesOver s.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal)
    (htv : Ideal.LiesOver t.1.maximalIdeal.asIdeal v.maximalIdeal.asIdeal) :
    letI := LocalCompletion.relativeAlgebra hsv
    letI := LocalCompletion.relativeAlgebra htv
    actualPaperRootNorm D s ^
        (1 / (Module.finrank (LocalCompletion.completionAt _ v)
          (LocalCompletion.completionAt _ s.1) : ℝ)) =
      actualPaperRootNorm D t ^
        (1 / (Module.finrank (LocalCompletion.completionAt _ v)
          (LocalCompletion.completionAt _ t.1) : ℝ)) := by
  let := LocalCompletion.relativeAlgebra hsv
  let := LocalCompletion.relativeAlgebra htv
  rw [LocalCompletion.inverse_relativeFinrank_eq_localDeg_ratio hsv,
    LocalCompletion.inverse_relativeFinrank_eq_localDeg_ratio htv,
    actualPaperRootNorm_eq_of_same_basePlace D s t hbase,
    (iutInitialThetaTorsionSource_degrees_eq_of_same_basePlace D s t hbase).2.2]

end
end JoshiTeich.Act1Scene1
