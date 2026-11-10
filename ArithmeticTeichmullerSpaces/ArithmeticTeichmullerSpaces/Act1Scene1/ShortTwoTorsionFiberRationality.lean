import ArithmeticTeichmullerSpaces.Act1Scene1.FullTorsionExtensionRationality

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: IUT-COR312-GEOMETRIC-TORSION-COUNT;
IUT-COR312-GEOMETRIC-TORSION-BASIS
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the existing Count fibre polynomial and multiplication formula, together with
full torsion cardinality on the same curve.
fidelity: a fibre root at the actual x coordinate of an actual nonsingular
point gives its n-multiple as the mapped rational two-torsion target. Full
rational n-torsion and odd n then give constant preimages for both coordinates
of that same point. No auxiliary point replaces its actual y coordinate.
Original composition of existing project theorems; no reference code copied.
boundary: short models only; normalization and residue-field transport remain
in the consuming modules.
-/

namespace JoshiTeich.Act1Scene1.ShortTwoTorsionFiberRationality

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open JoshiTeich.ReferenceIut.Anabelian
open JoshiTeich.ReferenceIut.Torsion
open scoped Classical

noncomputable section
universe u v

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]
  (K : Type v) [Field K] [Algebra k K]

/-- The actual point above a short-model fibre root multiplies to its two-torsion target. -/
theorem nsmul_eq_twoTorsion_of_root_short
    [CharZero K] [IsAlgClosed K]
    (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0)
    (n : ℕ) (hn : n ≠ 0)
    (R : E.toAffine.Point) (hR : R ≠ 0) (hTwo : 2 • R = 0)
    {x y : K} (hxy : (E⁄K).toAffine.Nonsingular x y)
    (hr : (fibrePoly (E⁄K) n (algebraMap k K (ptX R))).IsRoot x) :
    n • Point.some x y hxy = pointMap E (algebraMap k K) R := by
  letI : (E⁄K).IsElliptic := by
    change (E.map (algebraMap k K)).IsElliptic
    infer_instance
  cases R with
  | zero => exact (hR rfl).elim
  | some r s hRaff =>
    let b : E.toAffine.Point →+ (E⁄K).toAffine.Point :=
      pointMap E (algebraMap k K)
    have hTwo' : 2 • b (Point.some r s hRaff) = 0 := by
      rw [← map_nsmul, hTwo, map_zero]
    have hNeg : -b (Point.some r s hRaff) = b (Point.some r s hRaff) :=
      (eq_neg_iff_add_eq_zero.mpr (by simpa only [two_nsmul] using hTwo')).symm
    have ha₁' : (E⁄K).toAffine.a₁ = 0 := by
      simp [WeierstrassCurve.baseChange, ha₁]
    have ha₃' : (E⁄K).toAffine.a₃ = 0 := by
      simp [WeierstrassCurve.baseChange, ha₃]
    have hR' : (E⁄K).toAffine.Nonsingular
        (algebraMap k K r) (algebraMap k K s) :=
      (E.toAffine.map_nonsingular (algebraMap k K).injective r s).mpr hRaff
    have hb : b (Point.some r s hRaff) =
        Point.some (algebraMap k K r) (algebraMap k K s) hR' := rfl
    change (fibrePoly (E⁄K) n (algebraMap k K r)).IsRoot x at hr
    have hne := ΨSq_ne_zero_of_root ha₁' ha₃' n hn hr
    obtain ⟨X, Y, hXY, hnP, hX⟩ :=
      smul_eq_of_ΨSq_ne_zero ha₁' ha₃' hxy n hne
    have hXr : X = algebraMap k K r := by
      rw [IsRoot, eval_fibrePoly, ← hX] at hr
      exact mul_right_cancel₀ hne (by linear_combination hr)
    have hp : Point.some X Y hXY = b (Point.some r s hRaff) ∨
        Point.some X Y hXY = -b (Point.some r s hRaff) := by
      rw [hb]
      exact (Point.X_eq_iff (h₁ := hXY) (h₂ := hR')).mp hXr
    rcases hp with hp | hp
    · exact hnP.trans hp
    · exact hnP.trans (hp.trans hNeg)

/-- Both given coordinates of the same point have constant preimages. -/
theorem coordinates_rational_of_fibre_root_short [CharZero K] [IsAlgClosed K]
    (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0)
    (n : ℕ) (hn : n ≠ 0) (hodd : Odd n)
    (hcard : Nat.card (AddSubgroup.torsionBy E.toAffine.Point n) = n ^ 2)
    (R : E.toAffine.Point) (hR : R ≠ 0) (hTwo : 2 • R = 0)
    {x y : K} (hxy : (E⁄K).toAffine.Nonsingular x y)
    (hr : (fibrePoly (E⁄K) n (algebraMap k K (ptX R))).IsRoot x) :
    ∃ a b : k, algebraMap k K a = x ∧ algebraMap k K b = y := by
  exact FullTorsionExtensionRationality.coordinates_rational_of_nsmul_twoTorsion
    E K n hn hodd hcard R hTwo (Point.some x y hxy)
    (nsmul_eq_twoTorsion_of_root_short E K ha₁ ha₃ n hn R hR hTwo hxy hr)

end
end JoshiTeich.Act1Scene1.ShortTwoTorsionFiberRationality
