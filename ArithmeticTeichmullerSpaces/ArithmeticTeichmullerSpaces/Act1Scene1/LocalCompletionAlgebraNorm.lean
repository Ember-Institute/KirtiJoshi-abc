import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarDeterminant
import Mathlib.RingTheory.Norm.Defs

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-ALGEBRA-NORM
source: actual completion scalar-ball Haar/index calculation and p-adic
determinant/Haar, transported through a finite basis over the actual embedding.
fidelity: identifies the p-adic modulus of the algebraic norm with the raw
completion norm for nonzero contracting scalars. No isometric embedding or
NormedSpace structure for the raw completion norm is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField MeasureTheory
open scoped Classical Valued

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable (w : FinitePlace K) (hw : JoshiTeich.Prologue.Arithmetic.residueChar w = p)

theorem norm_algebraNorm_eq_completionNorm_of_contracting
    (x : completionAt K w) (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    letI := padicAlgebra hw
    ‖Algebra.norm ℚ_[p] x‖ = ‖x‖ := by
  letI := padicAlgebra hw
  letI : Module.Finite ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  letI : ContinuousSMul ℚ_[p] (completionAt K w) :=
    continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb hw)
  letI : IsModuleTopology ℚ_[p] (completionAt K w) := isModuleTopologyOfFiniteDimensional
  let b := Module.finBasis ℚ_[p] (completionAt K w)
  let e := b.equivFunL
  let f : completionAt K w ≃ₗ[ℚ_[p]] completionAt K w :=
    { toFun := fun y => x * y
      invFun := fun y => x⁻¹ * y
      left_inv := fun y => inv_mul_cancel_left₀ hx y
      right_inv := fun y => mul_inv_cancel_left₀ hx y
      map_add' := mul_add x
      map_smul' := fun a y => by simp [Algebra.smul_def, mul_left_comm] }
  let g := ((e.toLinearEquiv.symm.trans f).trans e.toLinearEquiv).toContinuousLinearEquiv
  let μ := normalizedHaar w
  let ν := μ.map e
  haveI : ν.IsAddHaarMeasure :=
    e.toLinearEquiv.toAddEquiv.isAddHaarMeasure_map μ e.continuous e.symm.continuous
  have hdet : LinearMap.det g.toLinearEquiv.toLinearMap = Algebra.norm ℚ_[p] x := by
    calc
      _ = LinearMap.det f.toLinearMap := LinearMap.det_conj f.toLinearMap e.toLinearEquiv
      _ = _ := by
        rw [← LinearMap.det_toMatrix b]
        exact (Algebra.norm_eq_matrix_det b x).symm
  let B : Set (completionAt K w) := Metric.closedBall 0 1
  have htransport (S : Set (completionAt K w)) : ν (e '' S) = μ S := by
    change (Measure.map e.toHomeomorph.toMeasurableEquiv μ) (e '' S) = _
    rw [MeasurableEquiv.map_apply]
    exact congrArg μ (e.injective.preimage_image S)
  have himage : e '' ((fun y => x * y) '' B) = g '' (e '' B) := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨e z, ⟨z, hz, rfl⟩, by simp [g, f]⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨x * z, ⟨z, hz, rfl⟩, by simp [g, f]⟩
  have hhaar : μ ((fun y => x * y) '' B) = ENNReal.ofReal ‖Algebra.norm ℚ_[p] x‖ := by
    rw [← htransport, himage, PadicHaar.measure_image_linearEquiv_eq_norm_det ν g,
      hdet, htransport, normalizedHaar_unitBall, mul_one]
  let z : integerRing w := ⟨x, Valued.toNormedField.norm_le_one_iff.mp hx1.le⟩
  have hz : z ≠ 0 := fun h => hx (congrArg (fun a : integerRing w => (a : completionAt K w)) h)
  have hlocal := normalizedHaar_scalarBall_toReal_eq_norm w z hz _
    (JoshiTeich.Prologue.Arithmetic.completionQOrder_valued w x hx hx1)
  change (μ ((fun y => x * y) '' B)).toReal = ‖x‖ at hlocal
  rw [hhaar, ENNReal.toReal_ofReal (norm_nonneg _)] at hlocal
  exact hlocal

end
end JoshiTeich.Act1Scene1.LocalCompletion
