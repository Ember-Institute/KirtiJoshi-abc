import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationDecomposition
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarNormalization

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SCALAR-RESIDUE-REGION
source: actual tensor normalization decomposition and Joshi III
componentwise principal-region shape (3568--3574).
fidelity: gives an exact residue-coordinate characterization of the actual
scalar normalization region as lambda_I times each residue integral closure.
Nonzero factor scalars give unit/nonzero multipliers; integral factor scalars
give integral multipliers. No arbitrary-set least hull or paper norm identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance coordinateIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])
variable (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)

include hz in
theorem pure_isUnit : IsUnit (P.pure z) := by
  refine ⟨⟨P.pure z, P.pure (fun i => (z i)⁻¹), ?_, ?_⟩, rfl⟩
  · rw [P.pure_mul]
    change P.pure (fun i => z i * (z i)⁻¹) = P.pure (fun _ => 1)
    exact congrArg P.pure (funext fun i => mul_inv_cancel₀ (hz i))
  · rw [P.pure_mul]
    change P.pure (fun i => (z i)⁻¹ * z i) = P.pure (fun _ => 1)
    exact congrArg P.pure (funext fun i => inv_mul_cancel₀ (hz i))

def scalarResidueMultiplier (I : MaximalSpectrum P.Tensor) : P.Tensor ⧸ I.asIdeal :=
  Ideal.Quotient.mk I.asIdeal (P.pure z)

include hz in
theorem scalarResidueMultiplier_isUnit (I : MaximalSpectrum P.Tensor) :
    IsUnit (P.scalarResidueMultiplier z I) :=
  (P.pure_isUnit z hz).map (Ideal.Quotient.mk I.asIdeal)

include hz in
theorem scalarResidueMultiplier_ne_zero (I : MaximalSpectrum P.Tensor) :
    P.scalarResidueMultiplier z I ≠ 0 := by
  haveI := I.isMaximal
  letI : Field (P.Tensor ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  exact (P.scalarResidueMultiplier_isUnit z hz I).ne_zero

theorem scalarResidueMultiplier_isIntegral (hz1 : ∀ i, ‖z i‖ ≤ 1)
    (I : MaximalSpectrum P.Tensor) : IsIntegral ℤ_[p] (P.scalarResidueMultiplier z I) := by
  have hunit : P.pure z ∈ P.unitLattice := P.pure_mem_lattice _ z
    (fun i => by simpa only [Metric.mem_closedBall, dist_zero_right] using hz1 i)
  exact IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) (Ideal.Quotient.mk I.asIdeal)
    (RingHom.ext fun _ => rfl) (P.isIntegral_of_mem_unitLattice hunit)

theorem mem_scalarNormalization_iff_residue_principal (x : P.Tensor) :
    x ∈ P.scalarNormalization z hz ↔ ∀ I : MaximalSpectrum P.Tensor,
      ∃ b : P.Tensor ⧸ I.asIdeal, IsIntegral ℤ_[p] b ∧
        P.scalarResidueMultiplier z I * b = Ideal.Quotient.mk I.asIdeal x := by
  constructor
  · rintro ⟨y, hy, rfl⟩ I
    refine ⟨Ideal.Quotient.mk I.asIdeal y,
      (P.isIntegral_iff_residue_integral y).mp hy I, ?_⟩
    change Ideal.Quotient.mk I.asIdeal (P.pure z) * Ideal.Quotient.mk I.asIdeal y =
      Ideal.Quotient.mk I.asIdeal (P.scale z hz y)
    rw [P.scale_eq_mul_pure, map_mul]
  · intro hx
    choose b hb heq using hx
    let y := P.residueDecomposition.symm b
    have hcoords (I : MaximalSpectrum P.Tensor) : Ideal.Quotient.mk I.asIdeal y = b I :=
      congrFun (P.residueDecomposition.apply_symm_apply b) I
    have hy : IsIntegral ℤ_[p] y := (P.isIntegral_iff_residue_integral y).mpr fun I => by
      rw [hcoords I]
      exact hb I
    refine ⟨y, hy, ?_⟩
    change P.scale z hz y = x
    apply P.eq_of_forall_residue_eq
    intro I
    rw [P.scale_eq_mul_pure, map_mul, hcoords I]
    exact heq I

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
