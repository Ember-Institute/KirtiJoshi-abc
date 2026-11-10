import ArithmeticTeichmullerSpaces.Act1Scene1.ShiftedDivisionCoordinatesIntegral
import ArithmeticTeichmullerSpaces.Act1Scene1.ShortDivisionFiberEquation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: the existing original pole-shift and division-coordinate arguments.
fidelity: combines the same affine point, coordinates, exact fibre equation
and strict target bound before actual specialization; no new hypothesis.
boundary: no residue specialization or residue-field rationality is asserted.
-/

namespace JoshiTeich.Act1Scene1.IntegralDivisionFiberData

open WeierstrassCurve JoshiTeich.ReferenceIut.Anabelian
open IntegralDivisionCoordinates
open scoped Classical
noncomputable section

variable {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
variable (E : WeierstrassCurve k)

/-- The original rational pole shift is nonzero. -/
theorem rational_shift_ne_zero
    (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
    (R : E.toAffine.Point) (hR0 : R ≠ 0) (hTwo : 2 • R = 0)
    (P : (E⁄K).toAffine.Point) (hx : ptX P ∉ W) :
    Affine.Point.add (W := (E⁄K).toAffine) P (pointMap E (algebraMap k K) R) ≠ 0 := by
  obtain ⟨x, y, h, heq, _⟩ :=
    ShiftedDivisionCoordinatesIntegral.rational_shift_affine E W hk R hR0 hTwo P hx
  exact fun hz => Affine.Point.some_ne_zero h (heq.symm.trans hz)

/-- The original rational pole shift has integral x-coordinate. -/
theorem rational_shift_x_mem
    (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
    (R : E.toAffine.Point) (hR0 : R ≠ 0) (hTwo : 2 • R = 0)
    (P : (E⁄K).toAffine.Point) (hx : ptX P ∉ W) :
    ptX (Affine.Point.add (W := (E⁄K).toAffine) P
      (pointMap E (algebraMap k K) R)) ∈ W := by
  obtain ⟨x, y, h, heq, hx'⟩ :=
    ShiftedDivisionCoordinatesIntegral.rational_shift_affine E W hk R hR0 hTwo P hx
  rw [heq]
  exact hx'

/-- Combine original integral coordinates, exact fibre equation and target residue bound. -/
theorem of_coordinates
    (W : ValuationSubring K) (n : ℕ) (P Q : (E⁄K).toAffine.Point) (r : K)
    (hcoords : ∃ (x y : K) (h : (E⁄K).toAffine.Nonsingular x y),
      Q = Affine.Point.some x y h ∧ x ∈ W ∧ y ∈ W)
    (hP : ptX P ∈ W)
    (heq : (((shortModel E)⁄K).Φ n).eval (ptX Q) -
      ptX P * (((shortModel E)⁄K).ΨSq n).eval (ptX Q) = 0)
    (hsmall : W.valuation (ptX P - r) < 1) :
    ∃ (x y : K) (h : (E⁄K).toAffine.Nonsingular x y),
      Q = Affine.Point.some x y h ∧ x ∈ W ∧ y ∈ W ∧ ptX P ∈ W ∧
      (((shortModel E)⁄K).Φ n).eval x -
        ptX P * (((shortModel E)⁄K).ΨSq n).eval x = 0 ∧
      W.valuation (ptX P - r) < 1 := by
  obtain ⟨x, y, h, hpoint, hx, hy⟩ := hcoords
  refine ⟨x, y, h, hpoint, hx, hy, hP, ?_, hsmall⟩
  simpa only [hpoint, ptX] using heq

end
end JoshiTeich.Act1Scene1.IntegralDivisionFiberData
