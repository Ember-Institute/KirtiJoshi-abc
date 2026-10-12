import ArithmeticTeichmullerSpaces.Act1Scene1.IutCyclicCoordinateField

/-!
source-id: JT-SCENE1-COMPLETION-LOG-FIBER-ACCOUNTING
source: S1.237 completion norm power law and Prologue/Core
`Arithmetic.sum_localDeg_liesOver`; Mathlib `Real.log_pow`.
fidelity: sums over every finite place above one base place. The actual ratio
consumer uses one descended element for all fibers. Paper representatives and
theta-volume accounting remain separate source obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue.Arithmetic NumberField
open scoped BigOperators Classical

universe u

noncomputable section

section Fiber

variable {F K : Type u} [Field F] [NumberField F]
  [Field K] [NumberField K] [Algebra F K]

theorem iutSum_relativeLocalDegree
    (w : FinitePlace F) (s : Finset (FinitePlace K))
    (hs : ∀ v, v ∈ s ↔
      Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    ∑ v ∈ s, relRamIdx v w * relInertDeg v w = Module.finrank F K := by
  apply Nat.eq_of_mul_eq_mul_left (localDeg_pos w)
  calc
    localDeg w * (∑ v ∈ s, relRamIdx v w * relInertDeg v w) =
        ∑ v ∈ s, localDeg v := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v hv =>
        (localDeg_eq_mul ((hs v).mp hv)).symm
    _ = Module.finrank F K * localDeg w := sum_localDeg_liesOver w s hs
    _ = localDeg w * Module.finrank F K := Nat.mul_comm _ _

/-- Every place in the full fiber contributes its relative ramification and
residue degree. Their sum is the extension degree. -/
theorem iutNegLog_norm_embedding_sum_liesOver
    (x : F) (w : FinitePlace F) (s : Finset (FinitePlace K))
    (hs : ∀ v, v ∈ s ↔
      Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) :
    (∑ v ∈ s, -Real.log ‖FinitePlace.embedding v.maximalIdeal (algebraMap F K x)‖) =
      (Module.finrank F K : ℝ) * (-Real.log ‖FinitePlace.embedding w.maximalIdeal x‖) := by
  classical
  calc
    _ = ∑ v ∈ s, (relRamIdx v w * relInertDeg v w : ℝ) *
        (-Real.log ‖FinitePlace.embedding w.maximalIdeal x‖) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvw := (hs v).mp hv
      rw [← iutEmbedCompletion_embedding hvw,
        iutEmbedCompletion_norm_eq_pow hvw, Real.log_pow]
      push_cast
      ring
    _ = (Module.finrank F K : ℝ) *
        (-Real.log ‖FinitePlace.embedding w.maximalIdeal x‖) := by
      rw [← Finset.sum_mul]
      have hDegree : (∑ v ∈ s, (relRamIdx v w * relInertDeg v w : ℝ)) =
          (Module.finrank F K : ℝ) := by
        exact_mod_cast iutSum_relativeLocalDegree w s hs
      rw [hDegree]

end Fiber

namespace IutCyclicCoordinate

open WeierstrassCurve

variable {F : Type u} [Field F] [NumberField F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (H : AddSubgroup (Affine.Point (Affine.baseChange E Fbar))) [Fintype H]

/-- The same descended ratio represents all full finite-place fibers. -/
theorem exists_ratioProduct_negLog_fiber_accounting
    (hgal : ∀ σ : Fbar ≃ₐ[F] Fbar, ∀ Q ∈ H,
      JoshiTeich.ReferenceIut.galPointMap F E Fbar σ Q ∈ H) :
    letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
      (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
    ∃ ρ : ↥(IutFourTorsion.field E Fbar),
      IntermediateField.inclusion (fourTorsionField_le E Fbar H) ρ =
        ratioProduct E Fbar H ∧
      ∀ (w : FinitePlace ↥(IutFourTorsion.field E Fbar))
        (s : Finset (FinitePlace ↥(field E Fbar H))),
        (∀ v, v ∈ s ↔ Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) →
        (∑ v ∈ s, -Real.log ‖FinitePlace.embedding v.maximalIdeal
          (ratioProduct E Fbar H)‖) =
          (Module.finrank ↥(IutFourTorsion.field E Fbar) ↥(field E Fbar H) : ℝ) *
            (-Real.log ‖FinitePlace.embedding w.maximalIdeal ρ‖) := by
  letI : Algebra (↥(IutFourTorsion.field E Fbar)) (↥(field E Fbar H)) :=
    (IntermediateField.inclusion (fourTorsionField_le E Fbar H)).toRingHom.toAlgebra
  obtain ⟨ρ, hρ⟩ := ratioProduct_eq_inclusion E Fbar H hgal
  refine ⟨ρ, hρ, ?_⟩
  intro w s hs
  rw [← hρ]
  exact iutNegLog_norm_embedding_sum_liesOver
    (F := ↥(IutFourTorsion.field E Fbar)) (K := ↥(field E Fbar H)) ρ w s hs

end IutCyclicCoordinate

end
end JoshiTeich.Act1Scene1
