import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeCoefficients
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRepresentativeBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-RAMIFICATION-GAP
source: actual q-root power equation, integer completion valuation, q-order
coprimality on VBad, and the computed representative coefficients.
fidelity: proves that actual VBad forces ell-divisible relative ramification
and a representative coefficient strictly below one. Its nonempty support
therefore gives a strict gap between the full normalized q-pilot and the
unweighted selected paper sum. No particular InitialThetaData is constructed.
The paper target and volume normalization still require source review.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue WithZero
open scoped BigOperators Classical Valued

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

theorem iutInitialThetaEll_dvd_qRootRelativeRamIdx_on_vbad
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hw : ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 ∈
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    D.prime.ℓ ∣ Arithmetic.relRamIdx s.1
      ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let b := R.basePlace s
  let e := Arithmetic.relRamIdx s.1 b.1
  have hmap : R.completionMap s = iutEmbedCompletion (R.liesOver s) := rfl
  have hpow := congrArg Valued.v (R.qroot_pow_eq s)
  rw [map_pow, hmap, iutValuedEmbedCompletion,
    iutCompletionQOrder_valued b.1 (B.tateParameter b)
      (B.tateParameter_ne_zero b) (B.tateParameter_norm_lt_one b)] at hpow
  change Valued.v (R.qroot s) ^ (2 * D.prime.ℓ) = exp (-(B.qOrder b : ℤ)) ^ e at hpow
  have hroot : Valued.v (R.qroot s) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (R.qroot_ne_zero s)
  rw [← exp_log hroot, ← exp_nsmul, ← exp_nsmul, exp_inj,
    nsmul_eq_mul, nsmul_eq_mul] at hpow
  push_cast at hpow
  have hdvdInt : (D.prime.ℓ : ℤ) ∣ (e : ℤ) * (B.qOrder b : ℤ) :=
    ⟨-(2 * log (Valued.v (R.qroot s))), by linear_combination hpow⟩
  have hdvd : D.prime.ℓ ∣ e * B.qOrder b := by exact_mod_cast hdvdInt
  have hcop := iutInitialThetaOddSupportBaseQPilotSource_qOrder_coprime_on_vbad D b hw
  exact (D.prime.ℓ_prime.dvd_mul.mp hdvd).resolve_right
    (D.prime.ℓ_prime.coprime_iff_not_dvd.mp hcop)

private theorem weight_le_one
    {F : Type u} [Field F] [NumberField F] (v : NumberField.FinitePlace F) :
    Arithmetic.qPilotWeight v ≤ 1 := by
  have h := Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter
    ({v} : Finset (NumberField.FinitePlace F)) (Arithmetic.residueChar v)
    (Arithmetic.residueChar_prime v)
  have hf : ({v} : Finset (NumberField.FinitePlace F)).filter
      (fun w => Arithmetic.residueChar w = Arithmetic.residueChar v) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact And.left
    · intro hw
      subst w
      exact ⟨rfl, rfl⟩
  rw [hf, Finset.sum_singleton] at h
  exact h

theorem iutInitialThetaRepresentativeCoefficient_lt_one_on_vbad
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : iutInitialThetaOddModSupportFinset D) (hv : v.1 ∈ D.VBad) :
    iutInitialThetaRepresentativeCoefficient D v < 1 := by
  let hv' := (iutInitialThetaOddModSupport_finite D).mem_toFinset.mp v.2
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v.1 hv'
  let b := R.basePlace s
  have hb : b.1 = iutInitialThetaSectionBasePlace D v.1 :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v.1 hv'
  have hbv : Ideal.LiesOver b.1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v.1
  have hw : b.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := ⟨v.1, hv, hbv⟩
  have hdiv := iutInitialThetaEll_dvd_qRootRelativeRamIdx_on_vbad D s hw
  have hEllLe : D.prime.ℓ ≤ Arithmetic.relRamIdx s.1 b.1 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero (R.liesOver s))) hdiv
  have hSource : (5 : ℝ) ≤ Arithmetic.relRamIdx s.1 b.1 := by
    exact_mod_cast D.prime.five_le.trans hEllLe
  have hBase : (1 : ℝ) ≤ Arithmetic.relRamIdx b.1 v.1 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Arithmetic.relRamIdx_ne_zero hbv)
  have hDen : (1 : ℝ) <
      (Arithmetic.relRamIdx b.1 v.1 : ℝ) * Arithmetic.relRamIdx s.1 b.1 := by
    nlinarith
  change Arithmetic.qPilotWeight v.1 /
    ((Arithmetic.relRamIdx b.1 v.1 : ℝ) * Arithmetic.relRamIdx s.1 b.1) < 1
  exact (div_lt_one (lt_trans (by norm_num) hDen)).mpr
    ((weight_le_one v.1).trans_lt hDen)

theorem iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaFullBaseQPilotLogSum D < iutInitialThetaSelectedQRootPaperSum D := by
  have hne : iutInitialThetaFullBaseQPilotLogSum D ≠ iutInitialThetaSelectedQRootPaperSum D := by
    intro h
    have hall := (iutInitialThetaFullBaseQPilotLogSum_eq_paperSum_iff_coefficients_eq_one D).mp h
    obtain ⟨v, hv⟩ := D.global.bad_nonempty
    have hfull : v ∈ iutInitialThetaOddModSupportFinset D :=
      (iutInitialThetaOddModSupport_finite D).mem_toFinset.mpr
        (iutInitialThetaVBad_subset_VBadOdd D hv)
    let vfull : iutInitialThetaOddModSupportFinset D := ⟨v, hfull⟩
    have hlt := iutInitialThetaRepresentativeCoefficient_lt_one_on_vbad D vfull hv
    rw [hall vfull] at hlt
    exact (lt_irrefl _ hlt)
  rcases lt_or_eq_of_le (iutInitialThetaFullBaseQPilotLogSum_le_selectedPaperSum D) with h | h
  · exact h
  · exact (hne h).elim

theorem iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) <
      iutInitialThetaSelectedQRootPaperSum D :=
  (iutInitialThetaReferenceAbsLogQ_le_fullBaseSum D).trans_lt
    (iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum D)

end
end JoshiTeich.Act1Scene1
