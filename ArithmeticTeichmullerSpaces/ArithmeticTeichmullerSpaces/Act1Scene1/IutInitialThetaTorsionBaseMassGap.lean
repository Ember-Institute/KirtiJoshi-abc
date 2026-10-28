import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionBaseDescent
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionSourceMassAudit

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-BASE-MASS-GAP
source: the actual bad-place nonemptiness and q-root ramification divisibility,
Galois equality of degree data over one base place, and the full-fibre mass
formula. Joshi III `eq:weights` supplies the representative-weight target.
fidelity: transports the strict torsion-source ramification defect to the
chosen base section and proves that one descended actual fibre has mass below
one. The coefficient is the actual q-pilot base weight divided by relative
ramification; no paper representative or mass-one certificate is assumed.
boundary: Scene1/Derived; fixed Initial Theta data and actual base carrier.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue NumberField
open scoped BigOperators
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

private theorem qPilotWeight_le_one
    (w : NumberField.FinitePlace D.F) : Arithmetic.qPilotWeight w ≤ 1 := by
  have h := Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter
    ({w} : Finset (NumberField.FinitePlace D.F)) (Arithmetic.residueChar w)
    (Arithmetic.residueChar_prime w)
  have hf : ({w} : Finset (NumberField.FinitePlace D.F)).filter
      (fun z => Arithmetic.residueChar z = Arithmetic.residueChar w) = {w} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact And.left
    · intro hz
      subst z
      exact ⟨rfl, rfl⟩
  rw [hf, Finset.sum_singleton] at h
  exact h

theorem iutInitialThetaTorsionSource_exists_relativeRamified :
    ∃ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
      1 < Arithmetic.relRamIdx s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  have hvOdd := iutInitialThetaVBad_subset_VBadOdd D hv
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := iutInitialThetaOddSupportSelectedQRootPlace D v hvOdd
  have hb : (R.basePlace s).1 = iutInitialThetaSectionBasePlace D v :=
    iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace D v hvOdd
  have hlies : Ideal.LiesOver (R.basePlace s).1.maximalIdeal.asIdeal
      v.maximalIdeal.asIdeal := by
    rw [hb]
    exact iutInitialThetaSectionBasePlace_liesOver D v
  have hbad : (R.basePlace s).1 ∈
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := ⟨v, hv, hlies⟩
  have hdiv := iutInitialThetaEll_dvd_qRootRelativeRamIdx_on_vbad D s hbad
  have hle : D.prime.ℓ ≤ Arithmetic.relRamIdx s.1 (R.basePlace s).1 :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero (R.liesOver s))) hdiv
  exact ⟨s, (lt_of_lt_of_le (by decide : 1 < 5) D.prime.five_le).trans_le hle⟩

theorem iutInitialThetaTorsionBaseSection_relRamIdx_eq_source
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Arithmetic.relRamIdx
        (iutInitialThetaTorsionBaseSection D
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s)).1
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 =
      Arithmetic.relRamIdx s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let b := R.basePlace s
  let t := iutInitialThetaTorsionBaseSection D b
  have ht : R.basePlace t = b := iutInitialThetaTorsionBaseSection_basePlace D b
  have hbase : R.basePlace s = R.basePlace t := by rw [ht]
  have hdeg := iutInitialThetaTorsionSource_degrees_eq_of_same_basePlace D s t hbase
  have hs := Arithmetic.ramIdx_eq_mul (R.liesOver s)
  have ht' := Arithmetic.ramIdx_eq_mul (R.liesOver t)
  rw [hbase] at hs
  have hprod' : Arithmetic.ramIdx (R.basePlace t).1 *
      Arithmetic.relRamIdx s.1 (R.basePlace t).1 =
      Arithmetic.ramIdx (R.basePlace t).1 *
        Arithmetic.relRamIdx t.1 (R.basePlace t).1 := by
    rw [← hs, ← ht', hdeg.1]
  have hprod : Arithmetic.ramIdx b.1 * Arithmetic.relRamIdx s.1 b.1 =
      Arithmetic.ramIdx b.1 * Arithmetic.relRamIdx t.1 b.1 := by
    simpa [ht] using hprod'
  simpa [b, t] using
    (Nat.eq_of_mul_eq_mul_left (Arithmetic.ramIdx_pos b.1) hprod).symm

theorem iutInitialTheta_exists_baseSection_mass_lt_one :
    ∃ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
      Arithmetic.qPilotWeight b.1 /
          (Arithmetic.relRamIdx (iutInitialThetaTorsionBaseSection D b).1 b.1 : ℝ) < 1 := by
  obtain ⟨s, hs⟩ := iutInitialThetaTorsionSource_exists_relativeRamified D
  let b := (iutInitialThetaOddSupportTorsionQRootSource D).basePlace s
  have hrel := iutInitialThetaTorsionBaseSection_relRamIdx_eq_source D s
  have hrelNat : Arithmetic.relRamIdx
      (iutInitialThetaTorsionBaseSection D b).1 b.1 =
      Arithmetic.relRamIdx s.1 b.1 := by
    simpa [b] using hrel
  have hrelR : (1 : ℝ) < Arithmetic.relRamIdx
      (iutInitialThetaTorsionBaseSection D b).1 b.1 := by
    rw [hrelNat]
    exact_mod_cast hs
  have hnum := qPilotWeight_le_one D b.1
  have hden : (0 : ℝ) < Arithmetic.relRamIdx
      (iutInitialThetaTorsionBaseSection D b).1 b.1 :=
    lt_trans zero_lt_one hrelR
  refine ⟨b, (div_lt_one hden).mpr ?_⟩
  exact hnum.trans_lt hrelR

end
end JoshiTeich.Act1Scene1
