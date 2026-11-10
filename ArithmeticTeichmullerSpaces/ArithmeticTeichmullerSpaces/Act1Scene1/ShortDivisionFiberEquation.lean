import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralDivisionCoordinates

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: IUT-COR312-GEOMETRIC-TORSION-COUNT;
IUT-COR312-GEOMETRIC-TORSION-BASIS
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the existing Count multiplication formula and completion of the square.
fidelity: the SAME point satisfying nQ=P has x-coordinate satisfying
Phi_n(X)-x(P)PsiSq_n(X)=0 on the completed-square model. Since the
completion fixes x, X and x(P) are the ORIGINAL coordinates. The shifted
consumer uses n(Q+R)=P+R and the existing pole-shift affine presentation.
Original composition of existing project theorems; no reference code copied.
boundary: no general-model polynomial invariance or residue-field identity.
-/

namespace JoshiTeich.Act1Scene1.ShortDivisionFiberEquation

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open JoshiTeich.ReferenceIut.Anabelian
open IntegralDivisionCoordinates
open scoped Classical
noncomputable section

/-- Descend a multiplication relation through its original injective group map. -/
theorem nsmul_eq_of_injective_map
    {A B : Type*} [AddMonoid A] [AddMonoid B]
    (f : A →+ B) (hf : Function.Injective f) (n : ℕ)
    {a a' : A} {b b' : B} (ha : f a = b) (ha' : f a' = b')
    (h : n • b = b') : n • a = a' := by
  apply hf
  rw [map_nsmul, ha, ha']
  exact h

variable {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
variable (E : WeierstrassCurve k)

/-- The exact multiplication-fibre equation, with original x coordinates and
division polynomials of the completed-square model. -/
theorem short_division_fibre_equation
    (n : ℕ) (P Q : (E⁄K).toAffine.Point) (hP : P ≠ 0) (hQ : n • Q = P) :
    (((shortModel E)⁄K).Φ n).eval (ptX Q) -
      ptX P * (((shortModel E)⁄K).ΨSq n).eval (ptX Q) = 0 := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  rcases P with _ | ⟨xg, yg, hG⟩
  · exact False.elim (hP rfl)
  rcases Q with _ | ⟨x, y, h⟩
  · change n • (0 : (E⁄K).toAffine.Point) = Point.some xg yg hG at hQ
    rw [smul_zero] at hQ
    exact False.elim (Point.some_ne_zero hG hQ.symm)
  change (((shortModel E)⁄K).Φ n).eval x -
    xg * (((shortModel E)⁄K).ΨSq n).eval x = 0
  have hshort : ∀ {x y : K}, (E⁄K).toAffine.Nonsingular x y →
      ((shortModel E)⁄K).toAffine.Nonsingular (vcX (squareChange E) x)
        (vcY (squareChange E) x y) := by
    intro x y hxy
    have ht := (nonsingular_vc (squareChange E) (E⁄K) x y).mp hxy
    rwa [squareChange_smul] at ht
  have ha₁₀ : (shortModel E).a₁ = 0 := IutGeometricTorsion.completeSquare_a₁ E
  have ha₃₀ : (shortModel E).a₃ = 0 := IutGeometricTorsion.completeSquare_a₃ E
  have ha₁ : ((shortModel E)⁄K).toAffine.a₁ = 0 := by
    simp [WeierstrassCurve.baseChange, ha₁₀]
  have ha₃ : ((shortModel E)⁄K).toAffine.a₃ = 0 := by
    simp [WeierstrassCurve.baseChange, ha₃₀]
  have hQshort := congrArg (toShort E) hQ
  rw [map_nsmul, toShort_some E h (hshort h),
    toShort_some E hG (hshort hG)] at hQshort
  have hne : (((shortModel E)⁄K).ΨSq n).eval (vcX (squareChange E) x) ≠ 0 := by
    intro hzero
    have hz := (JoshiTeich.ReferenceIut.Torsion.smul_eq_zero_iff_ΨSq
      ha₁ ha₃ (hshort h) n).mpr hzero
    rw [hz] at hQshort
    exact Point.some_ne_zero (hshort hG) hQshort.symm
  obtain ⟨X, Y, hXY, hnQ, hX⟩ :=
    JoshiTeich.ReferenceIut.Torsion.smul_eq_of_ΨSq_ne_zero
      ha₁ ha₃ (hshort h) n hne
  have hXg : X = vcX (squareChange E) xg := by
    rw [hnQ] at hQshort
    exact (Point.some.inj hQshort).1
  rw [hXg] at hX
  exact sub_eq_zero.mpr (by simpa only [squareChange_x] using hX.symm)

/-- Odd multiplication fixes the original rational two-torsion shift. -/
theorem shifted_nsmul
    (n : ℕ) (hodd : Odd n) (R : E.toAffine.Point) (hTwo : 2 • R = 0)
    (P Q : (E⁄K).toAffine.Point) (hQ : n • Q = P) :
    n • Point.add (W := (E⁄K).toAffine) Q (pointMap E (algebraMap k K) R) =
      Point.add (W := (E⁄K).toAffine) P (pointMap E (algebraMap k K) R) := by
  have hnR : n • R = R := by
    obtain ⟨m, rfl⟩ := hodd
    rw [add_nsmul, one_nsmul, mul_nsmul, hTwo, smul_zero, zero_add]
  let T : (E⁄K).toAffine.Point := pointMap E (algebraMap k K) R
  have hnT : n • T = T := by
    change n • pointMap E (algebraMap k K) R = pointMap E (algebraMap k K) R
    rw [← map_nsmul, hnR]
  change n • (Q + T) = P + T
  rw [nsmul_add, hQ, hnT]

end
end JoshiTeich.Act1Scene1.ShortDivisionFiberEquation
