import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeRamificationGap
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeFiberMass

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-SOURCE-MASS-AUDIT
source: Joshi III `ss:weighted-vol`, `eq:weights`; the actual Initial Theta
bad-place nonemptiness, q-order coprimality, q-root equation, and ramification
tower; the proved rational-prime q-pilot mass bound.
fidelity: produces a ramified torsion-source place from each supplied Initial
Theta datum. Its prime fibre has q-pilot mass below one, so no prime-preserving
map on this torsion source can have mass one in every representative fibre.
The source weights here are inertDeg/[torsion field : Q], not the paper's
inverse relative-completion-degree weights. No paper carrier is identified.
boundary: Scene1/Derived; does not assert existence of Initial Theta data or
rule out a representative construction with different weights or source.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators Classical

universe u v
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem iutInitialThetaEll_le_qRootRamIdx_on_vbad
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hw : ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 ∈
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    D.prime.ℓ ≤ Arithmetic.ramIdx s.1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  have hdiv := iutInitialThetaEll_dvd_qRootRelativeRamIdx_on_vbad D s hw
  have hle : D.prime.ℓ ≤ Arithmetic.relRamIdx s.1 (R.basePlace s).1 :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Arithmetic.relRamIdx_ne_zero (R.liesOver s))) hdiv
  rw [Arithmetic.ramIdx_eq_mul (R.liesOver s)]
  exact hle.trans (Nat.le_mul_of_pos_left _ (Arithmetic.ramIdx_pos _))

/-- Bad-place nonemptiness supplies the ramification witness; callers do not
need to assume a ramified source place separately. -/
theorem iutInitialTheta_exists_ramified_qRootSource :
    ∃ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
      1 < Arithmetic.ramIdx s.1 := by
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
  have hle := iutInitialThetaEll_le_qRootRamIdx_on_vbad D s hbad
  exact ⟨s, (lt_of_lt_of_le (by decide : 1 < 5) D.prime.five_le).trans_le hle⟩

theorem iutInitialThetaTorsionSource_exists_prime_mass_lt_one :
    ∃ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
      (∑ w ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset.filter
          (fun w => Arithmetic.residueChar w = Arithmetic.residueChar s.1),
        Arithmetic.qPilotWeight w) < 1 := by
  obtain ⟨s, hs⟩ := iutInitialTheta_exists_ramified_qRootSource D
  refine ⟨s, ?_⟩
  exact qPilotWeight_sum_lt_one_of_ramified_of_residueChar
    ((iutInitialThetaOddSupportTorsionQRootSource D).badFinset.filter
      (fun w => Arithmetic.residueChar w = Arithmetic.residueChar s.1))
    (Arithmetic.residueChar s.1) (Arithmetic.residueChar_prime s.1)
    (fun w hw => (Finset.mem_filter.mp hw).2)
    s.1 (Finset.mem_filter.mpr ⟨s.2, rfl⟩) hs

/-- This excludes mass one for this actual torsion source and its q-pilot
weights, without any q-log, volume, degree-one, or paper-term assumptions. -/
theorem iutInitialThetaTorsionSource_no_mass_one_prime_representatives
    {R : Type v} [DecidableEq R]
    (f : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset → R)
    (primeLabel : R → ℕ)
    (hPrime : ∀ w, Arithmetic.residueChar w.1 = primeLabel (f w)) :
    ¬ (∀ r : R,
      (∑ w : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        if f w = r then Arithmetic.qPilotWeight w.1 else 0) = 1) := by
  intro hmass
  obtain ⟨s, hs⟩ := iutInitialThetaTorsionSource_exists_prime_mass_lt_one D
  have hsum :
      (∑ w : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        if Arithmetic.residueChar w.1 = Arithmetic.residueChar s.1 then
          Arithmetic.qPilotWeight w.1 else 0) =
      ∑ w ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset.filter
          (fun w => Arithmetic.residueChar w = Arithmetic.residueChar s.1),
        Arithmetic.qPilotWeight w := by
    rw [Finset.sum_filter]
    refine Finset.sum_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
    · intro w _
      exact w.2
    · intro w _ z _ h
      exact Subtype.ext h
    · intro w hw
      exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
    · intro w _
      rfl
  have hle :
      (∑ w : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        if f w = f s then Arithmetic.qPilotWeight w.1 else 0) ≤
      ∑ w : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
        if Arithmetic.residueChar w.1 = Arithmetic.residueChar s.1 then
          Arithmetic.qPilotWeight w.1 else 0 := by
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : f w = f s
    · have hp : Arithmetic.residueChar w.1 = Arithmetic.residueChar s.1 := by
        rw [hPrime w, hPrime s, hw]
      simp only [if_pos hw, if_pos hp, le_refl]
    · simp only [if_neg hw]
      split_ifs
      · exact (Arithmetic.qPilotWeight_pos w.1).le
      · exact le_rfl
  rw [hmass (f s), hsum] at hle
  exact (not_le_of_gt hs) hle

end
end JoshiTeich.Act1Scene1
