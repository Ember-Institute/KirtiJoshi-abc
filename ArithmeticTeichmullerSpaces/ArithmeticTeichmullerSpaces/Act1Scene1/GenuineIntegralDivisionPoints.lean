import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralDivisionCoordinates
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Inertia.lean`, division-coordinate integrality.
fidelity: proves that both coordinates of every actual generic division point
are integral over k[xG]. Constructs those coordinates in the actual normalization
ring for the full division-coordinate field, with their original ambient values.
boundary: Scene1/Derived. This supplies coordinates for the later inertia proof;
unramified covering, AG.Orbicurve comparison and the producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The actual generic division coordinates are integral over the x-line ring. -/
theorem divSys_coordinates_isIntegral (n : ℕ) (hn : 0 < n) :
    IsIntegral (Algebra.adjoin k {xG E}) (ptX (divSys E n)) ∧
      IsIntegral (Algebra.adjoin k {xG E}) (ptY (divSys E n)) := by
  let B := Algebra.adjoin k {xG E}
  let R := (integralClosure B (Ω E)).restrictScalars k
  have hR : ∀ x : Ω E, IsIntegral R x → x ∈ R := by
    intro x hx
    change IsIntegral B x
    exact isIntegral_trans (R := B) (A := integralClosure B (Ω E)) x hx
  have hxg : xG E ∈ R :=
    (integralClosure B (Ω E)).algebraMap_mem
      ⟨xG E, Algebra.self_mem_adjoin_singleton k (xG E)⟩
  have hQ := nsmul_divSys E n hn
  generalize heq : divSys E n = Q at hQ ⊢
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨isIntegral_zero, isIntegral_zero⟩
  · exact IntegralDivisionCoordinates.division_coordinates_mem E R hR n hn h
      (nonsingular_generic E) hxg hQ

theorem Qpt_coordinates_isIntegral (ell : ℕ) :
    IsIntegral (Algebra.adjoin k {xG E}) (ptX (Qpt E ell)) ∧
      IsIntegral (Algebra.adjoin k {xG E}) (ptY (Qpt E ell)) :=
  divSys_coordinates_isIntegral E (effLevel ell) (effLevel_pos ell)

theorem Qpt_coordinates_mem_normalizationField (ell : ℕ) :
    ptX (Qpt E ell) ∈ normalizationField E ell ⊥ false ∧
      ptY (Qpt E ell) ∈ normalizationField E ell ⊥ false := by
  simp only [mem_normalizationField, stabilizerField_bot_false_eq_QField]
  exact ⟨IntermediateField.subset_adjoin _ _ (by simp),
    IntermediateField.subset_adjoin _ _ (by simp)⟩

local instance divisionNormalizationTower (ell : ℕ) :
    IsScalarTower (Algebra.adjoin k {xG E}) (normalizationField E ell ⊥ false) (Ω E) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual x coordinate as an element of the full division normalization ring. -/
def divisionNormalizationX (ell : ℕ) : coverCoordinateRing E ell ⊥ false :=
  ⟨⟨ptX (Qpt E ell), (Qpt_coordinates_mem_normalizationField E ell).1⟩,
    (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (Algebra.adjoin k {xG E})
        (normalizationField E ell ⊥ false) (Ω E))
      (algebraMap (normalizationField E ell ⊥ false) (Ω E)).injective).mp
        (Qpt_coordinates_isIntegral E ell).1⟩

/-- The actual y coordinate in the same normalization ring. -/
def divisionNormalizationY (ell : ℕ) : coverCoordinateRing E ell ⊥ false :=
  ⟨⟨ptY (Qpt E ell), (Qpt_coordinates_mem_normalizationField E ell).2⟩,
    (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (Algebra.adjoin k {xG E})
        (normalizationField E ell ⊥ false) (Ω E))
      (algebraMap (normalizationField E ell ⊥ false) (Ω E)).injective).mp
        (Qpt_coordinates_isIntegral E ell).2⟩

@[simp] theorem coe_divisionNormalizationX (ell : ℕ) :
    ((divisionNormalizationX E ell : normalizationField E ell ⊥ false) : Ω E) =
      ptX (Qpt E ell) := rfl

@[simp] theorem coe_divisionNormalizationY (ell : ℕ) :
    ((divisionNormalizationY E ell : normalizationField E ell ⊥ false) : Ω E) =
      ptY (Qpt E ell) := rfl

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
