import ArithmeticTeichmullerSpaces.Act1Scene1.IutSixTorsionTateRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionQOrderPower
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogCostAbsorption

/-!
source-id: JT-SCENE1-ACTUAL-SELECTED-QROOT-THREE-DIVISIBILITY
source: actual rational six-torsion, selected Tate uniformization and the
2ell-th-root equation; Joshi III initial theta data and 3190--3208.
fidelity: the selected Tate parameter has an actual sixth root in its
completion. Its integer order is divisible by six; as ell is prime >=5,
the actual selected q-root integer order is divisible by three and >=3.
boundary: Scene1/Derived; no ramification-normalized size bound is assumed.
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped Classical Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance (priority := 1100) selectedSixDecidableEq : DecidableEq ↥D.prime.torsionField :=
  fun a b => Classical.propDecidable (a = b)

theorem selectedTateParameter_has_sixth_root (v : iutInitialThetaOddModSupportFinset D) :
    let s := FullSupportPaperWeightedHull.selected D v
    ∃ r : PrincipalUnitKummer.localField D s,
      r ^ 6 = (iutInitialThetaOddSupportTorsionQRootSource D).qroot s ^ (2 * D.prime.ℓ) := by
  letI : IsAlgClosed D.Fbar := D.isAlgClosure.isAlgClosed
  let s := FullSupportPaperWeightedHull.selected D v
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := (iutInitialThetaTateFamilyOfTorsion D).S s.1
    (iutInitialThetaOddSupportTateFamily_badPlace_source D s)
  let g := iutWeierstrassPointMap (E := D.E) (algebraMap D.F ↥D.prime.torsionField)
  let f := iutWeierstrassPointMap (E := D.E.map (algebraMap D.F ↥D.prime.torsionField))
    (NumberField.FinitePlace.embedding s.1.maximalIdeal)
  have hsix : IutSixTorsionRational (F := D.F) (Fbar := D.Fbar) (E := D.E) := by
    exact D.global.six_torsion_rational
  obtain ⟨r, hr⟩ := exists_sixth_root_of_rational_six_torsion (Fbar := D.Fbar)
    (IutTateQuotientUniformization.ofTateStructure S) (f.comp g)
    ((iutWeierstrassPointMap_injective _).comp (iutWeierstrassPointMap_injective _)) hsix
  refine ⟨r, hr.trans ?_⟩
  exact (iutInitialThetaOddSupportTateFamily_q_eq_baseParameter D s).trans (R.qroot_pow_eq s).symm

theorem selectedQRoot_three_dvd_qOrder (v : iutInitialThetaOddModSupportFinset D) :
    3 ∣ Arithmetic.completionQOrder (FullSupportPaperWeightedHull.selected D v).1
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot (FullSupportPaperWeightedHull.selected D v)) := by
  let s := FullSupportPaperWeightedHull.selected D v
  let q := (iutInitialThetaOddSupportTorsionQRootSource D).qroot s
  have hq0 := (iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s
  have hq1 := iutInitialThetaFullQRoot_norm_lt_one D s
  have hell : 0 < 2 * D.prime.ℓ := by have h := D.prime.five_le; omega
  have hqn : ‖q ^ (2 * D.prime.ℓ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq1 hell.ne'
  obtain ⟨r, hr⟩ := selectedTateParameter_has_sixth_root D v
  have hd := LocalCompletion.qOrder_dvd_of_power_root s.1 _ (pow_ne_zero _ hq0) hqn 6 (by decide) r hr
  have hd3 := dvd_trans (by decide : 3 ∣ 6) hd
  rw [LocalCompletion.qOrder_pow s.1 q hq0 hq1 _ hell] at hd3
  have hcop : Nat.Coprime 3 (2 * D.prime.ℓ) := by
    apply Nat.Coprime.mul_right (by decide : Nat.Coprime 3 2)
    exact (Nat.coprime_primes Nat.prime_three D.prime.ℓ_prime).mpr
      (by have h := D.prime.five_le; omega)
  exact (Nat.prime_three.dvd_mul.mp hd3).resolve_left (Nat.prime_three.coprime_iff_not_dvd.mp hcop)

theorem selectedQRoot_qOrder_ge_three (v : iutInitialThetaOddModSupportFinset D) :
    3 ≤ Arithmetic.completionQOrder (FullSupportPaperWeightedHull.selected D v).1
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot (FullSupportPaperWeightedHull.selected D v)) :=
  Nat.le_of_dvd (Arithmetic.completionQOrder_pos _ _
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)
    (iutInitialThetaFullQRoot_norm_lt_one D _)) (selectedQRoot_three_dvd_qOrder D v)

theorem selectedPaperTerm_ge_three_log_prime (v : iutInitialThetaOddModSupportFinset D) :
    3 * Real.log (Arithmetic.residueChar (FullSupportPaperWeightedHull.selected D v).1) ≤
      OrdinaryKummerLogHull.selectedPaperTerm D v := by
  let s := FullSupportPaperWeightedHull.selected D v
  let q := (iutInitialThetaOddSupportTorsionQRootSource D).qroot s
  have ho := Arithmetic.ordp_eq_of_valued s.1 q _
    (Arithmetic.completionQOrder_valued s.1 q
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero s)
      (iutInitialThetaFullQRoot_norm_lt_one D s))
  have he : (Arithmetic.ramIdx s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.ramIdx_pos s.1).ne'
  have ht : OrdinaryKummerLogHull.selectedPaperTerm D v =
      (Arithmetic.completionQOrder s.1 q : ℝ) * Real.log (Arithmetic.residueChar s.1) := by
    rw [OrdinaryKummerLogHull.selectedPaperTerm, actualPaperRootNorm_negLog_eq_paperTerm, ho]
    push_cast
    dsimp only [s] at he ⊢
    field_simp [he]
    <;> ring
  rw [ht]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast selectedQRoot_qOrder_ge_three D v)
    (Real.log_nonneg (by exact_mod_cast (Arithmetic.residueChar_prime s.1).one_le))

end
end JoshiTeich.Act1Scene1
