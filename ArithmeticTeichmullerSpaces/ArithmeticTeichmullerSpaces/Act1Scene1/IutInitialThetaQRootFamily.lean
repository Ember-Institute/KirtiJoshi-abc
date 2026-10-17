import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperBallProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootIntegralThreshold
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRootAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-QROOT-FAMILY
source: `iut`: `refer/iut/Iut/Concrete/ThetaRegion.lean`, `ThetaLocalData`
and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`, `thetaLocalData`.
fidelity: constructs the global finite-place q-root family needed by that
interface from the actual torsion-field q-root source. Bad places use the real
root and all other places use `1`; support and nonnegative order are proved.
The concrete local-theory carrier, completion embeddings, and root power law
remain separate source obligations and are not hidden in this family.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

namespace IutInitialThetaQRootFamily

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def badChars : Finset ℕ :=
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset.image
    Arithmetic.residueChar

def qrootAt (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    v.maximalIdeal.adicCompletion ↥D.prime.torsionField := by
  classical
  exact if hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
      (iutInitialThetaOddSupportTorsionQRootSource D).qroot ⟨v, hv⟩
    else 1

theorem qrootAt_ne_zero
    (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    qrootAt D v ≠ 0 := by
  classical
  unfold qrootAt
  split_ifs with hv
  · exact (iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero ⟨v, hv⟩
  · exact one_ne_zero

theorem qrootAt_ordp_nonneg
    (v : NumberField.FinitePlace ↥D.prime.torsionField) :
    0 ≤ Arithmetic.ordp v (qrootAt D v) := by
  classical
  unfold qrootAt
  split_ifs with hv
  ·
    exact Arithmetic.ordp_nonneg_of_norm_le_one v
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot ⟨v, hv⟩)
      (iutInitialThetaFullQRoot_norm_lt_one D ⟨v, hv⟩).le
  · simp [Arithmetic.ordp]

theorem qrootAt_eq_one_of_residueChar_not_mem_badChars
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : Arithmetic.residueChar v ∉ badChars D) :
    qrootAt D v = 1 := by
  classical
  have hnot : v ∉
      (iutInitialThetaOddSupportTorsionQRootSource D).badFinset := by
    intro hmem
    apply hv
    exact Finset.mem_image.mpr ⟨v, hmem, rfl⟩
  simp [qrootAt, hnot]

theorem residueChar_mem_badChars_of_mem_badFinset
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Arithmetic.residueChar v ∈ badChars D := by
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem badChars_prime
    (p : ℕ) (hp : p ∈ badChars D) : p.Prime := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
  exact Arithmetic.residueChar_prime v

theorem qrootAt_pow_eq_of_mem_badFinset
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootAt D v ^ (2 * D.prime.ℓ) =
      (iutInitialThetaOddSupportTorsionQRootSource D).completionMap ⟨v, hv⟩
        ((iutInitialThetaOddSupportBaseQPilotSource D).tateParameter
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩)) := by
  unfold qrootAt
  split_ifs with h
  · exact (iutInitialThetaOddSupportTorsionQRootSource D).qroot_pow_eq ⟨v, hv⟩
  · exact (h hv).elim

theorem qrootAt_norm_lt_one_of_mem_badFinset
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ‖qrootAt D v‖ < 1 := by
  unfold qrootAt
  split_ifs with h
  · exact iutInitialThetaFullQRoot_norm_lt_one D ⟨v, h⟩
  · exact (h hv).elim

theorem qrootAt_pow_eq_admissiblePrime
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hw : ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace
      ⟨v, hv⟩).1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    qrootAt D v ^ (2 * D.prime.ℓ) =
      (iutInitialThetaOddSupportTorsionQRootSource D).completionMap ⟨v, hv⟩
        ((D.prime.tate
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩).1 hw).q) := by
  unfold qrootAt
  split_ifs with h
  · exact iutInitialThetaOddSupportTorsionQRootSource_qroot_pow_eq_admissiblePrime
      D ⟨v, h⟩ hw
  · exact (h hv).elim

theorem qrootAt_ordp_eq_baseQOrder
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hv : v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Arithmetic.ordp v (qrootAt D v) =
      ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩) : ℝ) /
        (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace ⟨v, hv⟩).1) := by
  unfold qrootAt
  split_ifs with h
  · simpa [PrincipalUnitKummer.baseIntegralThreshold] using
      (PrincipalUnitKummer.qroot_ordp_eq_baseQOrder D ⟨v, h⟩)
  · exact (h hv).elim

noncomputable def qrootAtWeightedFiber
    (p : ℕ) : ℝ := by
  classical
  letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Fintype.ofFinite _
  exact ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 *
      (if hv : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
        Arithmetic.ordp v.1 (qrootAt D v.1)
      else 0)

theorem qrootAtWeightedFiber_eq_baseQOrder
    (p : ℕ) :
    qrootAtWeightedFiber D p =
      ∑ w ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
        Arithmetic.qPilotWeight w.1 *
          ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
  classical
  letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Fintype.ofFinite _
  change (∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 *
      (if hv : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
        Arithmetic.ordp v.1 (qrootAt D v.1)
      else 0)) = _
  calc
    _ = ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
          Arithmetic.residueChar v = p},
        Arithmetic.placeWeight v.1 *
          (if hv : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset then
            Arithmetic.ordp v.1
              ((iutInitialThetaOddSupportTorsionQRootSource D).qroot ⟨v.1, hv⟩)
          else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases h : v.1 ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset
      · simp [h, qrootAt]
      · simp [h]
    _ = _ := IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder D p

end IutInitialThetaQRootFamily

end
end JoshiTeich.Act1Scene1
