import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeQRootSum
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedQRootAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-WEIGHTED-BOUND
source: the actual selected source/base contraction equivalence, q-root ordp
formula, arithmetic weight bound, and ramification tower identity.
fidelity: compares the actual selected weighted q-root log sum with its
unweighted paper-normalized sum and identifies the weighted sum with the
selected base q-order sum. Both results depend only on InitialThetaData;
coverage of the full base support and paper normalization remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

private theorem selected_ordp_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}) :
    Arithmetic.ordp s.1.1 ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1) =
      ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1) : ℝ) /
        (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s.1).1) := by
  rcases s.2 with ⟨v, hv, hplace⟩
  have hs : iutInitialThetaOddSupportSelectedQRootPlace D v hv = s.1 :=
    Subtype.ext hplace
  have h := iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder D v hv
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let statement : R.badFinset → Prop := fun t =>
    Arithmetic.ordp t.1 (R.qroot t) = (B.qOrder (R.basePlace t) : ℝ) /
      (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx (R.basePlace t).1)
  exact (congrArg statement hs).mp h

def iutInitialThetaSelectedWeightedQRootLogSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : ℝ :=
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  ∑ s : S, Arithmetic.qPilotWeight (R.basePlace s.1).1 *
    ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1)) *
      Real.log (Arithmetic.residueChar s.1.1)

theorem iutInitialThetaSelectedWeightedQRootLogSum_le_paperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaSelectedWeightedQRootLogSum D ≤ iutInitialThetaSelectedQRootPaperSum D := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  unfold iutInitialThetaSelectedWeightedQRootLogSum iutInitialThetaSelectedQRootPaperSum
  apply Finset.sum_le_sum
  intro s hs
  let b := (R.basePlace s.1).1
  have hWeight : Arithmetic.qPilotWeight b ≤ 1 := by
    have h := Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter
      ({b} : Finset (NumberField.FinitePlace D.F)) (Arithmetic.residueChar b)
      (Arithmetic.residueChar_prime b)
    have hf : ({b} : Finset (NumberField.FinitePlace D.F)).filter
        (fun w => Arithmetic.residueChar w = Arithmetic.residueChar b) = {b} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact And.left
      · intro hx
        subst x
        exact ⟨rfl, rfl⟩
    rw [hf, Finset.sum_singleton] at h
    exact h
  have hRam : (Arithmetic.ramIdx b : ℝ) ≤ Arithmetic.ramIdx s.1.1 := by
    have hrel := Arithmetic.relRamIdx_ne_zero (R.liesOver s.1)
    have h := Arithmetic.ramIdx_eq_mul (R.liesOver s.1)
    have hnat : Arithmetic.ramIdx b ≤ Arithmetic.ramIdx s.1.1 := by
      rw [h]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hrel)
    exact_mod_cast hnat
  have hOrd : 0 ≤ Arithmetic.ordp s.1.1 (R.qroot s.1) := by
    rw [selected_ordp_eq D s]
    positivity
  have hLog : 0 ≤ Real.log (Arithmetic.residueChar s.1.1) := by
    apply Real.log_nonneg
    exact_mod_cast (Arithmetic.residueChar_prime s.1.1).one_lt.le
  apply mul_le_mul_of_nonneg_right _ hLog
  calc
    Arithmetic.qPilotWeight b *
        ((Arithmetic.ramIdx b : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1)) ≤
        1 * ((Arithmetic.ramIdx b : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1)) :=
      mul_le_mul_of_nonneg_right hWeight (mul_nonneg (Nat.cast_nonneg _) hOrd)
    _ ≤ (Arithmetic.ramIdx s.1.1 : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1) := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hRam hOrd

theorem iutInitialThetaSelectedWeightedQRootLogSum_eq_baseQOrderSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaSelectedWeightedQRootLogSum D =
      let B := {b : NumberField.FinitePlace D.F // b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}
      letI : Fintype B := (iutInitialThetaOddSupportSelectedBasePlaces_finite D).fintype
      ∑ b : B, Arithmetic.qPilotWeight b.1 *
        ((iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log (Arithmetic.residueChar b.1) := by
  classical
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let S := {s : R.badFinset // s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  let W := {b : NumberField.FinitePlace D.F // b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}
  let : Fintype W := (iutInitialThetaOddSupportSelectedBasePlaces_finite D).fintype
  let e := iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv D
  have hterm (s : S) :
      Arithmetic.qPilotWeight (R.basePlace s.1).1 *
          ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1)) *
          Real.log (Arithmetic.residueChar s.1.1) =
        Arithmetic.qPilotWeight (e s).1 *
          ((iutInitialThetaOddSupportSelectedBaseQOrder D (e s) : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
            Real.log (Arithmetic.residueChar (e s).1) := by
    have hindex : iutInitialThetaOddSupportSelectedBaseQOrder D (e s) = B.qOrder (R.basePlace s.1) := by
      apply congrArg B.qOrder
      apply Subtype.ext
      rfl
    have hplace : (e s).1 = (R.basePlace s.1).1 := rfl
    rw [hindex, hplace, Arithmetic.residueChar_eq_of_liesOver (R.liesOver s.1), selected_ordp_eq D s]
    change Arithmetic.qPilotWeight (R.basePlace s.1).1 *
      ((Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) *
        ((B.qOrder (R.basePlace s.1) : ℝ) /
          (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx (R.basePlace s.1).1))) *
          Real.log (Arithmetic.residueChar (R.basePlace s.1).1) = _
    have hRam : (Arithmetic.ramIdx (R.basePlace s.1).1 : ℝ) ≠ 0 := by
      exact_mod_cast (Arithmetic.ramIdx_pos (R.basePlace s.1).1).ne'
    have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by
      have h := D.prime.five_le
      positivity
    field_simp [hRam, hEll]
  unfold iutInitialThetaSelectedWeightedQRootLogSum
  calc
    _ = ∑ s : S, Arithmetic.qPilotWeight (e s).1 *
        ((iutInitialThetaOddSupportSelectedBaseQOrder D (e s) : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
          Real.log (Arithmetic.residueChar (e s).1) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hterm s
    _ = _ := e.sum_comp (fun b => Arithmetic.qPilotWeight b.1 *
      ((iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
        Real.log (Arithmetic.residueChar b.1))

theorem iutInitialThetaSelectedBaseQOrderLogSum_le_paperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    let W := {b : NumberField.FinitePlace D.F // b ∈ iutInitialThetaOddSupportSelectedBasePlaces D}
    letI : Fintype W := (iutInitialThetaOddSupportSelectedBasePlaces_finite D).fintype
    (∑ b : W, Arithmetic.qPilotWeight b.1 *
      ((iutInitialThetaOddSupportSelectedBaseQOrder D b : ℝ) / (2 * (D.prime.ℓ : ℝ))) *
        Real.log (Arithmetic.residueChar b.1)) ≤ iutInitialThetaSelectedQRootPaperSum D := by
  have h := iutInitialThetaSelectedWeightedQRootLogSum_le_paperSum D
  rw [iutInitialThetaSelectedWeightedQRootLogSum_eq_baseQOrderSum D] at h
  exact h

end
end JoshiTeich.Act1Scene1
