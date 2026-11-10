import ArithmeticTeichmullerSpaces.Act1Scene1.IutGeometricTorsionBasis
import Mathlib.SetTheory.Cardinal.Finite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: the full torsion cardinality of the same actual seed; the geometric
torsion count already recorded under IUT-COR312-GEOMETRIC-TORSION-BASIS.
fidelity: the actual point map exhausts torsion in every algebraically closed
extension. An odd multiple above a rational two-torsion point is rational.
The final theorem gives constant preimages for both coordinates of that point.
boundary: the fibre-polynomial step producing the multiplication identity and
the normalization residue-field argument are separate obligations.
Original local proof; extracted from the earlier ShiftedFiberRationality draft.
-/

namespace JoshiTeich.Act1Scene1.FullTorsionExtensionRationality

open WeierstrassCurve
open JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

noncomputable section
universe u v

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]
  (K : Type v) [Field K] [Algebra k K]

/-- Restrict the actual point map to n-torsion on both sides. -/
def torsionBaseChangeMap (n : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point n →+
      AddSubgroup.torsionBy (E⁄K).toAffine.Point n := by
  let b : E.toAffine.Point →+ (E⁄K).toAffine.Point :=
    pointMap E (algebraMap k K)
  exact (b.domRestrict _).codRestrict _ fun T =>
    AddSubgroup.torsionBy.nsmul_iff.mpr (by
      change n • b T.val = 0
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp T.property, map_zero])

theorem torsionBaseChangeMap_injective (n : ℕ) :
    Function.Injective (torsionBaseChangeMap E K n) := by
  intro T U h
  apply Subtype.ext
  exact pointMap_injective E (algebraMap k K) (congrArg Subtype.val h)

/-- Full rational torsion cardinality exhausts torsion over any closed extension. -/
theorem torsionBaseChangeMap_surjective [IsAlgClosed K] (n : ℕ) (hn : n ≠ 0)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2) :
    Function.Surjective (torsionBaseChangeMap E K n) := by
  letI : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap k K).injective
  letI : (E⁄K).IsElliptic := by
    change (E.map (algebraMap k K)).IsElliptic
    infer_instance
  have hgeom : Nat.card (AddSubgroup.torsionBy (E⁄K).toAffine.Point n) = n ^ 2 :=
    iutGeometricTorsion_card (E⁄K) n hn
  letI : Finite (AddSubgroup.torsionBy (E⁄K).toAffine.Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hgeom]; exact pow_ne_zero 2 hn)
  exact ((Nat.bijective_iff_injective_and_card (torsionBaseChangeMap E K n)).mpr
    ⟨torsionBaseChangeMap_injective E K n, hcard.trans hgeom.symm⟩).surjective

lemma ptX_pointMap (P : E.toAffine.Point) :
    ptX (pointMap E (algebraMap k K) P) = algebraMap k K (ptX P) := by
  cases P with
  | zero =>
    change (0 : K) = algebraMap k K 0
    exact (map_zero (algebraMap k K)).symm
  | some x y h => rfl

lemma ptY_pointMap (P : E.toAffine.Point) :
    ptY (pointMap E (algebraMap k K) P) = algebraMap k K (ptY P) := by
  cases P with
  | zero =>
    change (0 : K) = algebraMap k K 0
    exact (map_zero (algebraMap k K)).symm
  | some x y h => rfl

/-- Every point whose odd n-multiple is the mapped rational two-torsion is rational. -/
theorem point_rational_of_nsmul_twoTorsion [IsAlgClosed K]
    (n : ℕ) (hn : n ≠ 0) (hodd : Odd n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2)
    (R : E.toAffine.Point) (hTwo : 2 • R = 0)
    (P : (E⁄K).toAffine.Point)
    (hP : n • P = pointMap E (algebraMap k K) R) :
    ∃ Q : E.toAffine.Point, pointMap E (algebraMap k K) Q = P := by
  let b : E.toAffine.Point →+ (E⁄K).toAffine.Point :=
    pointMap E (algebraMap k K)
  change n • P = b R at hP
  have hnR : n • R = R := by
    obtain ⟨m, rfl⟩ := hodd
    rw [add_nsmul, one_nsmul, mul_nsmul, hTwo, smul_zero, zero_add]
  have hT : n • (P - b R) = 0 := by
    rw [nsmul_sub, hP, ← map_nsmul, hnR, sub_self]
  let T : AddSubgroup.torsionBy (E⁄K).toAffine.Point n :=
    ⟨P - b R, AddSubgroup.torsionBy.nsmul_iff.mpr hT⟩
  obtain ⟨T₀, hT₀⟩ := torsionBaseChangeMap_surjective E K n hn hcard T
  have hT₀val : b T₀.val = P - b R := congrArg Subtype.val hT₀
  refine ⟨T₀.val + R, ?_⟩
  change b (T₀.val + R) = P
  rw [map_add, hT₀val, sub_add_cancel]

/-- Both coordinates of the same actual point have constant preimages. -/
theorem coordinates_rational_of_nsmul_twoTorsion [IsAlgClosed K]
    (n : ℕ) (hn : n ≠ 0) (hodd : Odd n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2)
    (R : E.toAffine.Point) (hTwo : 2 • R = 0)
    (P : (E⁄K).toAffine.Point)
    (hP : n • P = pointMap E (algebraMap k K) R) :
    ∃ a b : k, algebraMap k K a = ptX P ∧ algebraMap k K b = ptY P := by
  obtain ⟨Q, hQ⟩ := point_rational_of_nsmul_twoTorsion E K n hn hodd hcard R hTwo P hP
  refine ⟨ptX Q, ptY Q, ?_, ?_⟩
  · exact (ptX_pointMap E K Q).symm.trans (congrArg ptX hQ)
  · exact (ptY_pointMap E K Q).symm.trans (congrArg ptY hQ)

end
end JoshiTeich.Act1Scene1.FullTorsionExtensionRationality
