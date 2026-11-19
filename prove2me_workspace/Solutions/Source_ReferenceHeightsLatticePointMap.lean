import Solutions.Source_ReferenceHeightsLatticeModular

/-!
# Points of the short lattice model on the complex quotient

The point formulas and descent correspond to `Heights/LatticeAffinePoint.lean`
and `Heights/LatticeQuotientPoint.lean` at `721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Heights

open WeierstrassCurve
open AbcAdaptation.Reference.Iut.Anabelian (some_ext)
open scoped UpperHalfPlane Classical

private theorem latticePoint_equation (τ : ℍ) (z : ℂ)
    (hz : z ∉ (periodPair τ).lattice) :
    (latticeCurve τ).toAffine.Equation ((periodPair τ).weierstrassP z)
      ((periodPair τ).derivWeierstrassP z / 2) := by
  rw [Affine.equation_iff]
  simp only [latticeCurve, zero_mul, add_zero]
  have h := (periodPair τ).derivWeierstrassP_sq z hz
  linear_combination h / 4

private theorem latticePoint_nonsingular (τ : ℍ) (z : ℂ)
    (hz : z ∉ (periodPair τ).lattice) :
    (latticeCurve τ).toAffine.Nonsingular ((periodPair τ).weierstrassP z)
      ((periodPair τ).derivWeierstrassP z / 2) := by
  let _ : (latticeCurve τ).IsElliptic := latticeCurve_isElliptic τ
  exact Affine.equation_iff_nonsingular.mp (latticePoint_equation τ z hz)

/-- The affine formula away from the lattice and the point at infinity at each pole. -/
noncomputable def latticePointMap (τ : ℍ) (z : ℂ) : (latticeCurve τ).toAffine.Point :=
  if hz : z ∈ (periodPair τ).lattice then .zero
  else .some _ _ (latticePoint_nonsingular τ z hz)

theorem latticePointMap_of_mem {τ : ℍ} {z : ℂ} (hz : z ∈ (periodPair τ).lattice) :
    latticePointMap τ z = 0 := by
  simp [latticePointMap, hz, Affine.Point.zero_def]

theorem latticePointMap_of_notMem {τ : ℍ} {z : ℂ} (hz : z ∉ (periodPair τ).lattice) :
    latticePointMap τ z = .some _ _ (latticePoint_nonsingular τ z hz) := by
  simp [latticePointMap, hz]

private theorem latticePointMap_add_lattice (τ : ℍ) (z : ℂ)
    (w : (periodPair τ).lattice) : latticePointMap τ (z + w) = latticePointMap τ z := by
  have hm : z + (w : ℂ) ∈ (periodPair τ).lattice ↔ z ∈ (periodPair τ).lattice :=
    (periodPair τ).lattice.toAddSubgroup.add_mem_cancel_right w.2
  by_cases hz : z ∈ (periodPair τ).lattice
  · rw [latticePointMap_of_mem (hm.mpr hz), latticePointMap_of_mem hz]
  · rw [latticePointMap_of_notMem (fun hw => hz (hm.mp hw)), latticePointMap_of_notMem hz]
    exact some_ext ((periodPair τ).weierstrassP_add_coe z w)
      (congrArg (fun t : ℂ => t / 2) ((periodPair τ).derivWeierstrassP_add_coe z w))

abbrev LatticeQuotient (τ : ℍ) := ℂ ⧸ (periodPair τ).lattice.toAddSubgroup

/-- The Weierstrass point map on the additive quotient. -/
noncomputable def latticeQuotientPointMap (τ : ℍ) :
    LatticeQuotient τ → (latticeCurve τ).toAffine.Point :=
  fun q => Quotient.liftOn' q (latticePointMap τ) fun a b h => by
    rw [QuotientAddGroup.leftRel_apply] at h
    let w : (periodPair τ).lattice := ⟨-a + b, h⟩
    simpa [w, ← add_assoc] using (latticePointMap_add_lattice τ a w).symm

@[simp] theorem latticeQuotientPointMap_mk (τ : ℍ) (z : ℂ) :
    latticeQuotientPointMap τ (QuotientAddGroup.mk z) = latticePointMap τ z := rfl

/-- Additivity and bijectivity of this specific quotient map give the uniformization
required by the torsion bound. -/
theorem latticePointUniformization_of_map {τ : ℍ}
    (hadd : ∀ z w : ℂ, latticePointMap τ (z + w) = latticePointMap τ z + latticePointMap τ w)
    (hbij : Function.Bijective (latticeQuotientPointMap τ)) : LatticePointUniformization τ := by
  let f : LatticeQuotient τ →+ (latticeCurve τ).toAffine.Point :=
    { toFun := latticeQuotientPointMap τ
      map_zero' := latticePointMap_of_mem (zero_mem _)
      map_add' := by
        intro q r
        obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
        obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective r
        exact hadd z w }
  refine ⟨AddEquiv.ofBijective f hbij, ?_, ?_⟩
  · exact fun z hz => latticePointMap_of_mem hz
  · exact fun z hz => ⟨latticePoint_nonsingular τ z hz, latticePointMap_of_notMem hz⟩

end AbcAdaptation.Reference.Heights
