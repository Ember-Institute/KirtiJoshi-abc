import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltComparison

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.GeometricTiltComparison

noncomputable section

variable {C D : Type*} [NormedField C] [IsUltrametricDist C]
  [NormedField D] [IsUltrametricDist D]

/-- An element is one plus an integral multiple of the given natural number. -/
def IsPrimePrincipal (p : ℕ) (x : C) : Prop :=
  ∃ r : LocalGeometricFontaine.integerRing C, x = 1 + (p : C) * (r : C)

/-- A norm-power equivalence pulls an integral principal-unit witness back to its source. -/
theorem isPrimePrincipal_of_apply_eq
    (e : C ≃+* D) (d : ℕ) (hd : 0 < d) (hnorm : ∀ z : C, ‖e z‖ ^ d = ‖z‖)
    (p : ℕ) (x : C) (y : D) (hxy : e x = y)
    (hy : IsPrimePrincipal p y) : IsPrimePrincipal p x := by
  obtain ⟨r, hr⟩ := hy
  let t := integerEquiv e d hd hnorm
  have hcoeff : e ((t.symm r : LocalGeometricFontaine.integerRing C) : C) = (r : D) :=
    (e.apply_symm_apply r : e (e.symm r) = (r : D))
  refine ⟨t.symm r, e.injective ?_⟩
  calc
    e x = y := hxy
    _ = 1 + (p : D) * (r : D) := hr
    _ = e (1 + (p : C) * (t.symm r : LocalGeometricFontaine.integerRing C)) := by
      rw [map_add, map_one, map_mul, map_natCast, hcoeff]

end

end JoshiTeich.Act1Scene1.GeometricTiltComparison
