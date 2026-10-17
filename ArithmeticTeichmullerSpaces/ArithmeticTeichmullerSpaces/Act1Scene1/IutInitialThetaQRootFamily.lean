import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedPaperBallProduct

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

end IutInitialThetaQRootFamily

end
end JoshiTeich.Act1Scene1
