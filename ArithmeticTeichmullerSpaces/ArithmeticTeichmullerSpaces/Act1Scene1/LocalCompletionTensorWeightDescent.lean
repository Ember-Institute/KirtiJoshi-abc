import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScalarAction
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-WEIGHT-DESCENT
source: actual tensor multilinearity, the completion norm of p and Joshi III
ss:weighted-vol (3522--3543), where the weighted product is a function of a region.
fidelity: proves a necessary condition for raw completion norm products to
depend only on the tensor scalar lattice. Moving p between factors preserves
the region, so weight times absolute local degree must be constant. This is
an audit of the stated raw-norm convention, not an unconditional paper counterexample.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance descentFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance descentIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

/-- Put p in one factor and 1 in every other factor. -/
def primeAtScalar (i : ι) (j : ι) : P.Factor j :=
  if j = i then algebraMap ℚ_[p] (P.Factor j) (p : ℚ_[p]) else 1

theorem primeAtScalar_ne_zero (i j : ι) : P.primeAtScalar i j ≠ 0 := by
  by_cases h : j = i
  · rw [primeAtScalar, if_pos h]
    intro hzero
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    apply hp0
    apply (algebraMap ℚ_[p] (P.Factor j)).injective
    simpa using hzero
  · simp [primeAtScalar, h]

theorem primeAtScalar_lattice_eq (i j : ι) :
    P.scalarLattice (P.primeAtScalar i) = P.scalarLattice (P.primeAtScalar j) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply SetLike.coe_injective
  rw [← P.unitLattice_image_scale (P.primeAtScalar i) (P.primeAtScalar_ne_zero i),
    ← P.unitLattice_image_scale (P.primeAtScalar j) (P.primeAtScalar_ne_zero j)]
  have hf : (fun x : P.Tensor => P.scale (P.primeAtScalar i) (P.primeAtScalar_ne_zero i) x) =
      (fun x : P.Tensor => P.scale (P.primeAtScalar j) (P.primeAtScalar_ne_zero j) x) := by
    funext x
    change P.scaleAt i (p : ℚ_[p]) hp0 x = P.scaleAt j (p : ℚ_[p]) hp0 x
    rw [P.scaleAt_apply, P.scaleAt_apply]
  exact congrArg (fun f : P.Tensor → P.Tensor => f '' (P.unitLattice : Set P.Tensor)) hf

theorem factor_prime_norm_eq_inv_pow_localDeg (i : ι) :
    ‖algebraMap ℚ_[p] (P.Factor i) (p : ℚ_[p])‖ =
      (p : ℝ)⁻¹ ^ Arithmetic.localDeg (P.place i) := by
  have h := norm_residueChar_eq_inv_pow_localDeg (P.place i)
  rw [P.residueChar_eq i] at h
  simpa only [map_natCast] using h

/-- A product indexed by the factor presentation; descent to regions is not assumed. -/
def weightedScalarVolume (γ : ι → ℝ) (z : ∀ i, P.Factor i) : ℝ :=
  ∏ i, ‖z i‖ ^ γ i

theorem weightedScalarVolume_primeAt_eq (γ : ι → ℝ) (i : ι) :
    P.weightedScalarVolume γ (P.primeAtScalar i) =
      (p : ℝ)⁻¹ ^ ((Arithmetic.localDeg (P.place i) : ℝ) * γ i) := by
  unfold weightedScalarVolume
  have hfactor (j : ι) : ‖P.primeAtScalar i j‖ ^ γ j =
      if j = i then ‖algebraMap ℚ_[p] (P.Factor j) (p : ℚ_[p])‖ ^ γ j else 1 := by
    by_cases h : j = i <;> simp [primeAtScalar, h]
  simp_rw [hfactor]
  rw [Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_pos, P.factor_prime_norm_eq_inv_pow_localDeg]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr (Nat.cast_nonneg p))]

theorem weightedScalarVolume_primeAt_eq_iff (γ : ι → ℝ) (i j : ι) :
    P.weightedScalarVolume γ (P.primeAtScalar i) = P.weightedScalarVolume γ (P.primeAtScalar j) ↔
      (Arithmetic.localDeg (P.place i) : ℝ) * γ i =
        (Arithmetic.localDeg (P.place j) : ℝ) * γ j := by
  rw [P.weightedScalarVolume_primeAt_eq, P.weightedScalarVolume_primeAt_eq]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact Real.rpow_right_inj (inv_pos.mpr (lt_trans zero_lt_one hp1))
    (ne_of_lt (inv_lt_one_of_one_lt₀ hp1))

theorem weightedDegree_eq_of_prime_region_volume (γ : ι → ℝ)
    (V : Submodule ℤ_[p] P.Tensor → ℝ)
    (hV : ∀ i, V (P.scalarLattice (P.primeAtScalar i)) =
      P.weightedScalarVolume γ (P.primeAtScalar i)) (i j : ι) :
    (Arithmetic.localDeg (P.place i) : ℝ) * γ i =
      (Arithmetic.localDeg (P.place j) : ℝ) * γ j := by
  apply (P.weightedScalarVolume_primeAt_eq_iff γ i j).mp
  rw [← hV i, ← hV j, P.primeAtScalar_lattice_eq i j]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
