import ArithmeticTeichmullerSpaces.Act1Scene1.TwoTorsionTranslationIntegral
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.VariableChangePoint

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the exact general Weierstrass two-torsion addition formula.
fidelity: at a pole of x, the x-coordinate after the same rational two-torsion
shift is congruent to the shift's x-coordinate modulo the valuation maximal
ideal. This strengthens integral membership to its actual residue value.
Original proofs; no reference implementation copied.
boundary: no residue-field rationality or projective cusp identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.TwoTorsionPoleShiftResidue

open WeierstrassCurve WeierstrassCurve.Affine
open JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
noncomputable section
attribute [local instance 2000] Classical.propDecidable

variable {K : Type*} [Field K]

/-- The inverse of a pole minus an integral element has strictly small valuation. -/
theorem inverse_sub_lt_one (W : ValuationSubring K)
    {x r : K} (hx : x ∉ W) (hr : r ∈ W) :
    W.valuation ((x - r)⁻¹) < 1 := by
  have hd : x - r ∉ W := by
    intro hd
    exact hx (by simpa only [sub_add_cancel] using W.add_mem (x - r) r hd hr)
  exact W.mem_nonunits_iff.mp (W.inv_mem_nonunits_iff.mpr (Or.inr hd))

private theorem numerator_mem (E : WeierstrassCurve K) (W : ValuationSubring K)
    (ha₁ : E.a₁ ∈ W) (ha₂ : E.a₂ ∈ W) (ha₄ : E.a₄ ∈ W)
    {r s : K} (hr : r ∈ W) (hs : s ∈ W) :
    3 * r ^ 2 + 2 * E.a₂ * r + E.a₄ - E.a₁ * s ∈ W := by
  have h2 : (2 : K) ∈ W := natCast_mem W.toSubring 2
  have h3 : (3 : K) ∈ W := natCast_mem W.toSubring 3
  exact W.toSubring.sub_mem
    (W.add_mem _ _
      (W.add_mem _ _
        (W.mul_mem _ _ h3 (W.pow_mem hr 2))
        (W.mul_mem _ _ (W.mul_mem _ _ h2 ha₂) hr))
      ha₄)
    (W.mul_mem _ _ ha₁ hs)

/-- The exact translated x-coordinate differs from the rational shift by a nonunit. -/
theorem translated_addX_sub_lt_one (E : WeierstrassCurve K) (W : ValuationSubring K)
    (ha₁ : E.a₁ ∈ W) (ha₂ : E.a₂ ∈ W) (ha₄ : E.a₄ ∈ W)
    {x y r s : K} (hP : E.toAffine.Nonsingular x y)
    (hR : E.toAffine.Nonsingular r s) (hr : r ∈ W) (hs : s ∈ W)
    (hTwo : 2 • (Point.some r s hR : E.toAffine.Point) = 0) (hx : x ∉ W) :
    W.valuation (E.toAffine.addX x r (E.toAffine.slope x r y s) - r) < 1 := by
  have hxr : x ≠ r := by
    intro h
    exact hx (h ▸ hr)
  have hTwoY := TwoTorsionTranslationIntegral.twoTorsion_y_relation E hR hTwo
  rw [TwoTorsionTranslationIntegral.addX_twoTorsion E hP.left hR.left hTwoY hxr,
    add_sub_cancel_left, div_eq_mul_inv, map_mul]
  have hnum : W.valuation (3 * r ^ 2 + 2 * E.a₂ * r + E.a₄ - E.a₁ * s) ≤ 1 :=
    (W.valuation_le_one_iff _).mpr (numerator_mem E W ha₁ ha₂ ha₄ hr hs)
  calc
    _ ≤ 1 * W.valuation ((x - r)⁻¹) :=
      mul_le_mul_of_nonneg_right hnum zero_le
    _ < 1 := by simpa only [one_mul] using inverse_sub_lt_one W hx hr

/-- The translated point is affine, and its x-coordinate reduces to the same rational r. -/
theorem translated_affine_x_sub_lt_one (E : WeierstrassCurve K) (W : ValuationSubring K)
    (ha₁ : E.a₁ ∈ W) (ha₂ : E.a₂ ∈ W) (ha₄ : E.a₄ ∈ W)
    {x y r s : K} (hP : E.toAffine.Nonsingular x y)
    (hR : E.toAffine.Nonsingular r s) (hr : r ∈ W) (hs : s ∈ W)
    (hTwo : 2 • (Point.some r s hR : E.toAffine.Point) = 0) (hx : x ∉ W) :
    ∃ (x' y' : K) (h' : E.toAffine.Nonsingular x' y'),
      Point.some x y hP + Point.some r s hR = Point.some x' y' h' ∧
      x' ∈ W ∧ W.valuation (x' - r) < 1 := by
  have hxr : x ≠ r := by
    intro h
    exact hx (h ▸ hr)
  have hadd := Point.add_of_X_ne (W := E.toAffine) (h₁ := hP) (h₂ := hR) hxr
  have hsmall := translated_addX_sub_lt_one E W ha₁ ha₂ ha₄ hP hR hr hs hTwo hx
  refine ⟨_, _, _, hadd, ?_, hsmall⟩
  have hdiff : E.toAffine.addX x r (E.toAffine.slope x r y s) - r ∈ W :=
    (W.valuation_le_one_iff _).mp hsmall.le
  exact (by simpa only [sub_add_cancel] using
    W.add_mem _ r hdiff hr)

variable {k : Type*} [Field k] [Algebra k K]

/-- A rational two-torsion shift has its original x-coordinate as the pole-limit residue. -/
theorem ptX_add_pointMap_sub_lt_one
    (E : WeierstrassCurve k) (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W)
    (R : E.toAffine.Point) (hR0 : R ≠ 0) (hTwo : 2 • R = 0)
    (P : (E⁄K).toAffine.Point) (hx : ptX P ∉ W) :
    W.valuation (ptX (Point.add (W := (E⁄K).toAffine) P
        (pointMap E (algebraMap k K) R)) -
      algebraMap k K (ptX R)) < 1 := by
  rcases P with _ | ⟨x, y, hP⟩
  · exact False.elim (hx W.zero_mem)
  rcases R with _ | ⟨r, s, hR⟩
  · exact False.elim (hR0 rfl)
  let i : E.toAffine.Point →+ (E⁄K).toAffine.Point :=
    pointMap E (algebraMap k K)
  let T : (E⁄K).toAffine.Point := i (Point.some r s hR)
  have hTK : 2 • T = 0 := by
    simpa only [T, map_nsmul, map_zero] using congrArg i hTwo
  have hT : (E⁄K).toAffine.Nonsingular (algebraMap k K r) (algebraMap k K s) :=
    (E.toAffine.map_nonsingular (f := algebraMap k K)
      (algebraMap k K).injective r s).mpr hR
  have hTeq : T = Point.some (algebraMap k K r) (algebraMap k K s) hT := rfl
  obtain ⟨x', y', h', hshift, _, hsmall⟩ :=
    translated_affine_x_sub_lt_one (E⁄K) W
      (hk E.a₁) (hk E.a₂) (hk E.a₄)
      hP hT (hk r) (hk s) (by simpa only [← hTeq] using hTK) hx
  change W.valuation (ptX (Point.some x y hP + T) -
    algebraMap k K r) < 1
  rw [hTeq, hshift]
  exact hsmall

end
end JoshiTeich.Act1Scene1.TwoTorsionPoleShiftResidue
