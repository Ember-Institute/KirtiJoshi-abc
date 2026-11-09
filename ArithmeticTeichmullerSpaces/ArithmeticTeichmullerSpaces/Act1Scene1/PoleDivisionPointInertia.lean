import ArithmeticTeichmullerSpaces.Act1Scene1.TwoTorsionTranslationIntegral
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PointMap

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
original local point argument from the exact Weierstrass addition formula.
fidelity: at a pole, translation by the same nonzero rational two-torsion
point moves the base point into the integral chart. Odd multiplication
preserves the shift, and the already proved integral-chart inertia theorem
then fixes the original division point. No reference implementation copied.
boundary: this is a pointwise valuation-inertia theorem. Its application to
an actual finite normalization prime must supply the existing inertia bridge;
it asserts no ambient lift, cusp, or theta-root identity.
-/

namespace JoshiTeich.Act1Scene1.PoleDivisionPointInertia

open WeierstrassCurve JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u v
noncomputable section

private theorem odd_nsmul_of_two_nsmul_eq_zero
    {A : Type*} [AddCommMonoid A] (n : ℕ) (hn : Odd n)
    (a : A) (ha : 2 • a = 0) : n • a = a := by
  obtain ⟨m, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul, ha, smul_zero, zero_add]

variable {k : Type u} [Field k] [CharZero k]
  {K : Type v} [Field K] [Algebra k K]
  (E : WeierstrassCurve k) [E.IsElliptic]

/-- Inertia fixes division points of an affine pole after an original rational shift. -/
theorem inertia_fixes_of_nsmul_pole
    (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
    (σ : K →ₐ[k] K) (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1)
    (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (R : E.toAffine.Point) (hR0 : R ≠ 0) (hTwo : 2 • R = 0)
    {xg yg : K} (hG : (E⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∉ W)
    (hσG : Affine.Point.map (W' := E) (S := k) σ
      (Affine.Point.some xg yg hG) = Affine.Point.some xg yg hG)
    (Q : (E⁄K).toAffine.Point)
    (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E) (S := k) σ Q = Q := by
  rcases R with _ | ⟨r, s, hR⟩
  · exact False.elim (hR0 rfl)
  let i : E.toAffine.Point →+ (E⁄K).toAffine.Point :=
    pointMap E (algebraMap k K)
  let T : (E⁄K).toAffine.Point := i (Affine.Point.some r s hR)
  have hTK : 2 • T = 0 := by
    simpa only [T, map_nsmul, map_zero] using congrArg i hTwo
  have hnT : n • T = T := odd_nsmul_of_two_nsmul_eq_zero n hodd T hTK
  have hT : (E⁄K).toAffine.Nonsingular (algebraMap k K r) (algebraMap k K s) :=
    (E.toAffine.map_nonsingular (f := algebraMap k K) (algebraMap k K).injective r s).mpr hR
  have hTeq : T = Affine.Point.some (algebraMap k K r) (algebraMap k K s) hT := rfl
  have hσT : Affine.Point.map (W' := E) (S := k) σ T = T := by
    rw [hTeq]
    exact some_ext (σ.commutes r) (σ.commutes s)
  obtain ⟨x', y', h', hshift, hx'⟩ :=
    TwoTorsionTranslationIntegral.translated_x_mem (E⁄K) W
      (hk E.a₁) (hk E.a₂) (hk E.a₄) hG hT (hk r) (hk s)
      (by simpa only [← hTeq] using hTK) hxg
  have hshift' : Affine.Point.some xg yg hG + T = Affine.Point.some x' y' h' := by
    simpa only [hTeq] using hshift
  have hσShift : Affine.Point.map (W' := E) (S := k) σ
      (Affine.Point.some x' y' h') = Affine.Point.some x' y' h' := by
    rw [← hshift', map_add, hσG, hσT]
  have hnShift : n • (Q + T) = Affine.Point.some x' y' h' := by
    rw [nsmul_add, hQ, hnT]
    exact hshift'
  have hfix := DivisionPointInertia.inertia_fixes_of_nsmul_valuation E W hk σ hσ
    n hn h' hx' hσShift (Q + T) hnShift
  rw [map_add, hσT] at hfix
  exact add_right_cancel hfix

end
end JoshiTeich.Act1Scene1.PoleDivisionPointInertia
