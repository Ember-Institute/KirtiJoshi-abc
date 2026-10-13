import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScale
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Lattice

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-INTEGRAL-BASIS
source: actual compact open integral tensor lattices; finite-dimensional
p-adic coordinates and Mathlib finite torsion-free modules over a PID.
fidelity: proves bounded integral submodules finitely generated, and
positive-radius tensor lattices full and free. This constructs integral
bases needed for finite-index calculations, not a maximal order or hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField
open scoped BigOperators

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance basisFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance basisFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance basisIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])
local instance basisIndexFinite : Fintype P.BasisIndex := by classical infer_instance

instance tensorIntegralScalarTower : IsScalarTower ℤ_[p] ℚ_[p] P.Tensor :=
  ⟨fun r s x => by change ((r : ℚ_[p]) * s) • x = (r : ℚ_[p]) • (s • x); rw [mul_smul]⟩

local instance basisScalarTower : IsScalarTower ℤ_[p] ℚ_[p] P.Tensor :=
  tensorIntegralScalarTower P

instance tensorIntegralTorsionFree : Module.IsTorsionFree ℤ_[p] P.Tensor := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x h
  change (r : ℚ_[p]) • x = 0 at h
  rcases smul_eq_zero.mp h with hr | hx
  · exact Or.inl (Subtype.coe_injective hr)
  · exact Or.inr hx

/-- A bounded integral submodule embeds in a finite module of integral coordinates. -/
theorem bounded_module_finite (L : Submodule ℤ_[p] P.Tensor)
    (hL : Bornology.IsBounded (L : Set P.Tensor)) : Module.Finite ℤ_[p] L := by
  classical
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hL
  have hp1 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (|C| + 1) by positivity) hp1
  have hp0 : (p : ℚ_[p]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hcoord (x : L) (k : P.BasisIndex) :
      ‖(p : ℚ_[p]) ^ m * P.tensorBasis.equivFun x k‖ ≤ 1 := by
    have hx : ‖P.tensorBasis.equivFun x k‖ ≤ |C| :=
      (norm_le_pi_norm (P.tensorBasis.equivFun x) k).trans
        ((hC x x.property).trans (le_abs_self C))
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (1 / (|C| + 1)) * |C| := mul_le_mul hm.le hx (norm_nonneg _) (by positivity)
      _ ≤ 1 := by rw [one_div, ← div_eq_inv_mul, div_le_one (by positivity)]; linarith
  let f : L →ₗ[ℤ_[p]] (P.BasisIndex → ℤ_[p]) :=
    { toFun := fun x k => ⟨(p : ℚ_[p]) ^ m * P.tensorBasis.equivFun x k, hcoord x k⟩
      map_add' := by
        intro x y
        ext k
        change (p : ℚ_[p]) ^ m * P.tensorBasis.equivFun (x + y) k = _
        simp only [Submodule.coe_add, map_add, Pi.add_apply, mul_add]
        rfl
      map_smul' := by
        intro r x
        ext k
        change (p : ℚ_[p]) ^ m * P.tensorBasis.equivFun ((r : ℚ_[p]) • (x : P.Tensor)) k =
          (r : ℚ_[p]) * ((p : ℚ_[p]) ^ m * P.tensorBasis.equivFun x k)
        rw [map_smul, Pi.smul_apply, smul_eq_mul]
        ring }
  apply Module.Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply P.tensorBasis.equivFun.injective
  funext k
  have h := congrArg (fun v : P.BasisIndex → ℤ_[p] => (v k : ℚ_[p])) hxy
  exact mul_left_cancel₀ hp0 h

theorem lattice_balls_span_eq_top (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    Submodule.span ℚ_[p]
      (P.lattice (fun i => Metric.closedBall 0 (r i)) : Set P.Tensor) = ⊤ := by
  classical
  obtain ⟨M, hM⟩ := P.exists_pow_smul_tensorBasis_mem_lattice r hr
  have hp0 : (p : ℚ_[p]) ^ M ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hBasis (k : P.BasisIndex) : P.tensorBasis k ∈
      Submodule.span ℚ_[p] (P.lattice (fun i => Metric.closedBall 0 (r i)) : Set P.Tensor) := by
    have h := Submodule.smul_mem
      (Submodule.span ℚ_[p] (P.lattice (fun i => Metric.closedBall 0 (r i)) : Set P.Tensor))
      ((p : ℚ_[p]) ^ M)⁻¹ (Submodule.subset_span (hM k))
    simpa only [smul_smul, inv_mul_cancel₀ hp0, one_smul] using h
  apply eq_top_iff.mpr
  rw [← P.tensorBasis.span_eq]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hBasis)

theorem lattice_balls_isLattice (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i ≤ 1) :
    @Submodule.IsLattice ℤ_[p] _ ℚ_[p] _ _ P.Tensor _ (basisIntegralModule P) _
      (tensorIntegralScalarTower P) (tensorIntegralScalarTower P)
      (P.lattice (fun i => Metric.closedBall 0 (r i))) := by
  have hbound := P.unitLattice_isBounded.subset
    (P.lattice_mono (fun i => Metric.closedBall_subset_closedBall (hr1 i)))
  have hfinite := P.bounded_module_finite _ hbound
  exact @Submodule.IsLattice.mk ℤ_[p] _ ℚ_[p] _ _ P.Tensor _ (basisIntegralModule P) _
    (tensorIntegralScalarTower P) (tensorIntegralScalarTower P) _
    (Module.Finite.iff_fg.mp hfinite) (P.lattice_balls_span_eq_top r hr)

theorem unitLattice_module_finite : Module.Finite ℤ_[p] P.unitLattice :=
  P.bounded_module_finite _ P.unitLattice_isBounded

theorem lattice_balls_module_free (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i ≤ 1) :
    Module.Free ℤ_[p] (P.lattice (fun i => Metric.closedBall 0 (r i))) := by
  let L := P.lattice (fun i => Metric.closedBall 0 (r i))
  letI : Module.Finite ℤ_[p] L := P.bounded_module_finite L
    (P.unitLattice_isBounded.subset (P.lattice_mono
      (fun i => Metric.closedBall_subset_closedBall (hr1 i))))
  letI : Module.IsTorsionFree ℤ_[p] P.Tensor := tensorIntegralTorsionFree P
  exact Module.free_of_finite_type_torsion_free'

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
