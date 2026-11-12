import ArithmeticTeichmullerSpaces.Act1Scene1.DivisionPointInertia

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's exact Weierstrass addition formula and the existing division-point inertia proof.
fidelity: translation by a nonzero rational two-torsion point moves an affine
point with nonintegral x into the integral affine chart. The formula holds
for the original general Weierstrass equation, with no change of model.
boundary: local point algebra used by the infinity inertia consumer; no new
geometry or ramification law is supplied.
-/

namespace JoshiTeich.Act1Scene1.TwoTorsionTranslationIntegral

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- Translation by a two-torsion point on the original Weierstrass model. -/
theorem addX_twoTorsion {x y r s : K}
    (hP : E.toAffine.Equation x y) (hR : E.toAffine.Equation r s)
    (hTwo : 2 * s + E.a₁ * r + E.a₃ = 0) (hxr : x ≠ r) :
    E.toAffine.addX x r (E.toAffine.slope x r y s) =
      r + (3 * r ^ 2 + 2 * E.a₂ * r + E.a₄ - E.a₁ * s) / (x - r) := by
  rw [slope_of_X_ne hxr, addX]
  rw [E.toAffine.equation_iff] at hP hR
  field_simp [sub_ne_zero.mpr hxr]
  linear_combination hP - hR - (y - s) * hTwo

/-- A two-torsion point satisfies its exact linear y-coordinate equation. -/
theorem twoTorsion_y_relation {r s : K} (hR : E.toAffine.Nonsingular r s)
    (hTwo : 2 • (Point.some r s hR : E.toAffine.Point) = 0) :
    2 * s + E.a₁ * r + E.a₃ = 0 := by
  have hNeg : -(Point.some r s hR : E.toAffine.Point) = Point.some r s hR := by
    exact (eq_neg_iff_add_eq_zero.mpr (by simpa only [two_nsmul] using hTwo)).symm
  rw [Point.neg_some] at hNeg
  have hy := (Point.some.inj hNeg).2
  change E.toAffine.negY r s = s at hy
  simp only [negY] at hy
  linear_combination -hy

/-- At a pole of x, the translated point has an integral affine x-coordinate. -/
theorem translated_x_mem (W : ValuationSubring K)
    (ha₁ : E.a₁ ∈ W) (ha₂ : E.a₂ ∈ W) (ha₄ : E.a₄ ∈ W)
    {x y r s : K} (hP : E.toAffine.Nonsingular x y)
    (hR : E.toAffine.Nonsingular r s) (hr : r ∈ W) (hs : s ∈ W)
    (hTwo : 2 • (Point.some r s hR : E.toAffine.Point) = 0) (hx : x ∉ W) :
    ∃ (x' y' : K) (h' : E.toAffine.Nonsingular x' y'),
      Point.some x y hP + Point.some r s hR = Point.some x' y' h' ∧ x' ∈ W := by
  have hxr : x ≠ r := by intro h; exact hx (h ▸ hr)
  have hd : x - r ∉ W := by
    intro hd
    have h := W.add_mem (x - r) r hd hr
    exact hx (by simpa only [sub_add_cancel] using h)
  have hinv : (x - r)⁻¹ ∈ W := (W.mem_or_inv_mem (x - r)).resolve_left hd
  have hTwoY := twoTorsion_y_relation E hR hTwo
  have hadd := Point.add_of_X_ne (W := E.toAffine) (h₁ := hP) (h₂ := hR) hxr
  refine ⟨_, _, _, hadd, ?_⟩
  rw [addX_twoTorsion E hP.left hR.left hTwoY hxr, div_eq_mul_inv]
  have h1 : (1 : K) ∈ W := W.one_mem
  have h2 : (2 : K) ∈ W := by
    convert W.add_mem 1 1 h1 h1 using 1 <;> norm_num
  have h3 : (3 : K) ∈ W := by
    convert W.add_mem 2 1 h2 h1 using 1 <;> norm_num
  exact W.add_mem r ((3 * r ^ 2 + 2 * E.a₂ * r + E.a₄ - E.a₁ * s) * (x - r)⁻¹)
    hr (W.mul_mem _ _
      (W.toSubring.sub_mem
        (W.add_mem _ _
          (W.add_mem _ _
            (W.mul_mem _ _ h3 (W.pow_mem hr 2))
            (W.mul_mem _ _ (W.mul_mem _ _ h2 ha₂) hr))
          ha₄)
        (W.mul_mem _ _ ha₁ hs))
      hinv)

end
end JoshiTeich.Act1Scene1.TwoTorsionTranslationIntegral
