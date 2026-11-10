import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralDivisionCoordinates
import ArithmeticTeichmullerSpaces.Act1Scene1.ShortTwoTorsionFiberRationality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: IUT-COR312-GEOMETRIC-TORSION-COUNT;
IUT-COR312-GEOMETRIC-TORSION-BASIS
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
completion of the square and the actual-point short-fibre rationality theorem.
fidelity: both GIVEN coordinates on the ORIGINAL model have constant preimages
when the same x is a root of the completed-square fibre over the same rational
two-torsion point. Only the given x and y are mapped into AlgebraicClosure L.
Completion preserves x and changes y by its explicit linear formula. The short
rational y is changed back before descending along the injective L-to-closure
map. No new point, prime, valuation, or residue certificate is supplied.
Original composition of existing project theorems; no reference code copied.
boundary: coordinate rationality only; no upper residue-field or degree claim.
-/

namespace JoshiTeich.Act1Scene1.OriginalShiftedFiberResidueRationality

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open JoshiTeich.ReferenceIut.Anabelian JoshiTeich.ReferenceIut.Torsion
open IntegralDivisionCoordinates
open scoped Classical

noncomputable section
universe u v

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

private lemma ptX_completeSquare (P : E.toAffine.Point) :
    ptX (vcEquiv (IutGeometricTorsion.completeSquare E) E P) = ptX P := by
  change ptX (vcPoint (IutGeometricTorsion.completeSquare E) E P) = ptX P
  cases P with
  | zero => rfl
  | some x y h =>
    change vcX (IutGeometricTorsion.completeSquare E) x = x
    simp [vcX, IutGeometricTorsion.completeSquare]

private lemma squareChange_y (K : Type v) [Field K] [Algebra k K] (x y : K) :
    vcY (squareChange E) x y =
      y + (algebraMap k K E.a₁ * x + algebraMap k K E.a₃) / 2 := by
  simp [vcY, squareChange, IutGeometricTorsion.completeSquare, VariableChange.map,
    map_ofNat] <;> ring

/-- Completion of the square keeps the given point and recovers its original y. -/
private theorem coordinates_rational_in_algClosed
    (K : Type v) [Field K] [Algebra k K] [CharZero K] [IsAlgClosed K]
    (n : ℕ) (hn : n ≠ 0) (hodd : Odd n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2)
    (R : E.toAffine.Point) (hR : R ≠ 0) (hTwo : 2 • R = 0)
    {x y : K} (hEq : (E⁄K).toAffine.Equation x y)
    (hRoot : (fibrePoly ((shortModel E)⁄K) n
      (algebraMap k K (ptX R))).IsRoot x) :
    ∃ a b : k, algebraMap k K a = x ∧ algebraMap k K b = y := by
  letI : (E⁄K).IsElliptic := by
    change (E.map (algebraMap k K)).IsElliptic
    infer_instance
  letI : (shortModel E).IsElliptic := by
    change (IutGeometricTorsion.completeSquare E • E).IsElliptic
    infer_instance
  have hxy : (E⁄K).toAffine.Nonsingular x y :=
    (E⁄K).toAffine.equation_iff_nonsingular.mp hEq
  have hshort : ((shortModel E)⁄K).toAffine.Nonsingular x
      (vcY (squareChange E) x y) := by
    have ht := (nonsingular_vc (squareChange E) (E⁄K) x y).mp hxy
    simpa only [squareChange_smul, squareChange_x] using ht
  let e := vcEquiv (IutGeometricTorsion.completeSquare E) E
  have hcard' : Nat.card
      (AddSubgroup.torsionBy (shortModel E).toAffine.Point n) = n ^ 2 := by
    rw [← Nat.card_congr (IutGeometricTorsion.torsionEquiv e n).toEquiv]
    exact hcard
  have hR' : e R ≠ 0 := by
    intro h
    exact hR (e.injective (h.trans (map_zero e).symm))
  have hTwo' : 2 • e R = 0 := by
    rw [← map_nsmul, hTwo, map_zero]
  have hRoot' : (fibrePoly ((shortModel E)⁄K) n
      (algebraMap k K (ptX (e R)))).IsRoot x := by
    simpa only [show ptX (e R) = ptX R from ptX_completeSquare E R] using hRoot
  obtain ⟨a, b, ha, hb⟩ :=
    ShortTwoTorsionFiberRationality.coordinates_rational_of_fibre_root_short
      (shortModel E) K (IutGeometricTorsion.completeSquare_a₁ E)
      (IutGeometricTorsion.completeSquare_a₃ E)
      n hn hodd hcard' (e R) hR' hTwo' hshort hRoot'
  rw [squareChange_y] at hb
  refine ⟨a, b - (E.a₁ * a + E.a₃) / 2, ha, ?_⟩
  calc
    algebraMap k K (b - (E.a₁ * a + E.a₃) / 2) =
        algebraMap k K b -
          (algebraMap k K E.a₁ * algebraMap k K a + algebraMap k K E.a₃) / 2 := by
      simp only [map_sub, map_div₀, map_add, map_mul, map_ofNat]
    _ = y := by rw [ha, hb]; ring

private lemma fibrePoly_baseChange
    (L : Type v) [Field L] [Algebra k L]
    (K : Type*) [Field K] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (n : ℕ) (r : L) :
    fibrePoly (E⁄K) n (algebraMap L K r) =
      (fibrePoly (E⁄L) n r).map (algebraMap L K) := by
  have hBC : (E⁄L).map (algebraMap L K) = E⁄K :=
    E.map_baseChange (IsScalarTower.toAlgHom k L K)
  rw [← hBC]
  simp only [fibrePoly, map_Φ, map_ΨSq, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C]

/-- Both original coordinates are rational over the original coefficient field. -/
theorem coordinates_rational
    (L : Type v) [Field L] [Algebra k L]
    (n : ℕ) (hn : n ≠ 0) (hodd : Odd n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2)
    (R : E.toAffine.Point) (hR : R ≠ 0) (hTwo : 2 • R = 0)
    {x y : L} (hEq : (E⁄L).toAffine.Equation x y)
    (hRoot : (fibrePoly ((shortModel E)⁄L) n
      (algebraMap k L (ptX R))).IsRoot x) :
    ∃ a b : k, algebraMap k L a = x ∧ algebraMap k L b = y := by
  let K := AlgebraicClosure L
  letI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap k L).injective
  letI : CharZero K := inferInstanceAs (CharZero (AlgebraicClosure L))
  have hBC : (E⁄L).map (algebraMap L K) = E⁄K :=
    E.map_baseChange (IsScalarTower.toAlgHom k L K)
  have hEqK : (E⁄K).toAffine.Equation
      (algebraMap L K x) (algebraMap L K y) := by
    have hm := hEq.map (algebraMap L K)
    change ((E⁄L).map (algebraMap L K)).toAffine.Equation
      (algebraMap L K x) (algebraMap L K y) at hm
    rwa [hBC] at hm
  have hRootK : (fibrePoly ((shortModel E)⁄K) n
      (algebraMap k K (ptX R))).IsRoot (algebraMap L K x) := by
    have hm := hRoot.map (f := algebraMap L K)
    rw [← fibrePoly_baseChange (shortModel E) L K,
      ← IsScalarTower.algebraMap_apply k L K] at hm
    exact hm
  obtain ⟨a, b, ha, hb⟩ :=
    coordinates_rational_in_algClosed E K n hn hodd hcard R hR hTwo hEqK hRootK
  refine ⟨a, b, ?_, ?_⟩
  · apply (algebraMap L K).injective
    simpa only [← IsScalarTower.algebraMap_apply k L K] using ha
  · apply (algebraMap L K).injective
    simpa only [← IsScalarTower.algebraMap_apply k L K] using hb

end
end JoshiTeich.Act1Scene1.OriginalShiftedFiberResidueRationality
