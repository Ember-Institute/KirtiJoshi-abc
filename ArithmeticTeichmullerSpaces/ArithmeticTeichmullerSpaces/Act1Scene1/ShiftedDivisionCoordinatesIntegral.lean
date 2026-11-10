import ArithmeticTeichmullerSpaces.Act1Scene1.TwoTorsionPoleShiftResidue

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the existing integral division-coordinate theorem and the exact two-torsion shift.
fidelity: for the same division point Q and rational shift R, odd multiplication
gives n(Q+R)=G+R. The pole shift makes G+R affine with integral x, so both
coordinates of Q+R belong to the original valuation ring. No inertia is needed.
Original composition of existing project theorems; no reference code copied.
boundary: does not assert rational residues or normalization residue-field identity.
-/

namespace JoshiTeich.Act1Scene1.ShiftedDivisionCoordinatesIntegral

open WeierstrassCurve WeierstrassCurve.Affine
open JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
noncomputable section
attribute [local instance 2000] Classical.propDecidable

variable {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
variable (E : WeierstrassCurve k)

/-- For a nonzero affine point the canonical coordinates satisfy nonsingularity. -/
theorem nonsingular_ptX_ptY (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) :
    (E⁄K).toAffine.Nonsingular (ptX P) (ptY P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact False.elim (hP rfl)
  · exact h

/-- A nonzero point is its same canonical-coordinate affine presentation. -/
theorem some_ptX_ptY (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) :
    Point.some (ptX P) (ptY P) (nonsingular_ptX_ptY E P hP) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact False.elim (hP rfl)
  · rfl

private theorem odd_nsmul_of_two_nsmul_eq_zero
    {A : Type*} [AddCommMonoid A] (n : ℕ) (hn : Odd n)
    (a : A) (ha : 2 • a = 0) : n • a = a := by
  obtain ⟨m, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul, ha, smul_zero, zero_add]

/-- Division above a nonzero integral affine point has both coordinates in the valuation ring. -/
theorem coordinates_mem_of_nsmul
    (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
    (n : ℕ) (hn : 0 < n) (P Q : (E⁄K).toAffine.Point)
    (hP : P ≠ 0) (hxP : ptX P ∈ W) (hQ : n • Q = P) :
    ptX Q ∈ W ∧ ptY Q ∈ W := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨W.zero_mem, W.zero_mem⟩
  have hPN := nonsingular_ptX_ptY E P hP
  have hQP : n • Point.some x y h =
      Point.some (ptX P) (ptY P) hPN :=
    hQ.trans (some_ptX_ptY E P hP).symm
  exact IntegralDivisionCoordinates.division_coordinates_mem E
    (DivisionPointInertia.valuationSubalgebra W hk)
    (DivisionPointInertia.valuationSubalgebra_integrallyClosed W hk)
    n hn h hPN hxP hQP

/-- A pole shifted by the same nonzero rational two-torsion point is affine with integral x. -/
theorem rational_shift_affine
    (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
    (R : E.toAffine.Point) (hR0 : R ≠ 0) (hTwo : 2 • R = 0)
    (P : (E⁄K).toAffine.Point) (hx : ptX P ∉ W) :
    ∃ (x' y' : K) (h' : (E⁄K).toAffine.Nonsingular x' y'),
      Point.add (W := (E⁄K).toAffine) P (pointMap E (algebraMap k K) R) = Point.some x' y' h' ∧ x' ∈ W := by
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
  obtain ⟨x', y', h', hshift, hx', _⟩ :=
    TwoTorsionPoleShiftResidue.translated_affine_x_sub_lt_one (E⁄K) W
      (hk E.a₁) (hk E.a₂) (hk E.a₄)
      hP hT (hk r) (hk s) (by simpa only [← hTeq] using hTK) hx
  refine ⟨x', y', h', ?_, hx'⟩
  change Point.some x y hP + T = Point.some x' y' h'
  simpa only [hTeq] using hshift

/-- The shifted SAME division point has integral x and y at the pole valuation. -/
theorem shifted_division_coordinates_mem
    (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
    (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (R : E.toAffine.Point) (hR0 : R ≠ 0) (hTwo : 2 • R = 0)
    (P Q : (E⁄K).toAffine.Point) (hx : ptX P ∉ W) (hQ : n • Q = P) :
    ptX (Point.add (W := (E⁄K).toAffine) Q (pointMap E (algebraMap k K) R)) ∈ W ∧
      ptY (Point.add (W := (E⁄K).toAffine) Q (pointMap E (algebraMap k K) R)) ∈ W := by
  let i : E.toAffine.Point →+ (E⁄K).toAffine.Point :=
    pointMap E (algebraMap k K)
  let T := i R
  have hTK : 2 • T = 0 := by
    simpa only [T, map_nsmul, map_zero] using congrArg i hTwo
  have hnT : n • T = T := odd_nsmul_of_two_nsmul_eq_zero n hodd T hTK
  obtain ⟨x', y', h', hshift, hx'⟩ := rational_shift_affine E W hk R hR0 hTwo P hx
  have hPshift : P + T ≠ 0 := by
    rw [show P + T = Point.some x' y' h' from hshift]
    exact Point.some_ne_zero h'
  have hxPshift : ptX (P + T) ∈ W := by
    rw [show P + T = Point.some x' y' h' from hshift]
    exact hx'
  have hnShift : n • (Q + T) = P + T := by
    rw [nsmul_add, hQ, hnT]
  exact coordinates_mem_of_nsmul E W hk n hn (P + T) (Q + T)
    hPshift hxPshift hnShift

/-- The same shifted division point is nonzero, so its two integral coordinates are an affine chart. -/
theorem shifted_division_ne_zero
    (W : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ W)
    (n : ℕ) (hodd : Odd n)
    (R : E.toAffine.Point) (hR0 : R ≠ 0) (hTwo : 2 • R = 0)
    (P Q : (E⁄K).toAffine.Point) (hx : ptX P ∉ W) (hQ : n • Q = P) :
    Point.add (W := (E⁄K).toAffine) Q (pointMap E (algebraMap k K) R) ≠ 0 := by
  let i : E.toAffine.Point →+ (E⁄K).toAffine.Point :=
    pointMap E (algebraMap k K)
  let T := i R
  have hTK : 2 • T = 0 := by
    simpa only [T, map_nsmul, map_zero] using congrArg i hTwo
  have hnT : n • T = T := odd_nsmul_of_two_nsmul_eq_zero n hodd T hTK
  obtain ⟨x', y', h', hshift, _⟩ := rational_shift_affine E W hk R hR0 hTwo P hx
  intro hzero
  have hnShift : n • (Q + T) = P + T := by
    rw [nsmul_add, hQ, hnT]
  have hshift' : P + T = Point.some x' y' h' := hshift
  rw [show Q + T = 0 from hzero, smul_zero, hshift'] at hnShift
  exact Point.some_ne_zero h' hnShift.symm

end
end JoshiTeich.Act1Scene1.ShiftedDivisionCoordinatesIntegral
