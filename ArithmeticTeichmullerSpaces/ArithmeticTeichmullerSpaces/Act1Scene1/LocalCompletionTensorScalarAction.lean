import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorScale

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SCALAR-ACTION
source: actual PiTensorProduct multilinearity and factor scaling.
fidelity: proves that multiplying one factor by a scalar induces the
corresponding scalar action on the whole tensor. This distinguishes the
one-factor tensor scalar action used by p-adic Haar scaling from the common
factor scaling map whose determinant has an extra factor-count exponent.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField
open scoped TensorProduct

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

local instance actionFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance actionFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)

def scaleAt (i₀ : ι) (a : ℚ_[p]) (ha : a ≠ 0) :
    P.Tensor ≃ₗ[ℚ_[p]] P.Tensor :=
  letI := Classical.decEq ι
  P.scale (fun i => if i = i₀ then algebraMap ℚ_[p] (P.Factor i) a else 1)
    (fun i => by
      by_cases h : i = i₀
      · subst i
        intro hzero
        apply ha
        apply (algebraMap ℚ_[p] (P.Factor i₀)).injective
        simpa using hzero
      · simp [h])

theorem scaleAt_apply (i₀ : ι) (a : ℚ_[p]) (ha : a ≠ 0) (x : P.Tensor) :
    P.scaleAt i₀ a ha x = a • x := by
  classical
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    rw [map_smul]
    change r • P.scaleAt i₀ a ha (P.pure f) = a • (r • P.pure f)
    rw [scaleAt, P.scale_pure]
    have hupdate :
        (fun i => (if i = i₀ then algebraMap ℚ_[p] (P.Factor i) a else 1) * f i) =
          Function.update f i₀ ((algebraMap ℚ_[p] (P.Factor i₀) a) * f i₀) := by
      funext i
      by_cases h : i = i₀
      · subst i
        simp
      · simp [h]
    rw [hupdate]
    have hscale :
        (PiTensorProduct.tprod ℚ_[p])
            (Function.update f i₀ ((algebraMap ℚ_[p] (P.Factor i₀) a) * f i₀)) =
          a • (PiTensorProduct.tprod ℚ_[p]) f := by
      rw [PiTensorProduct.tprod_eq_tprodCoeff_one]
      rw [show (algebraMap ℚ_[p] (P.Factor i₀) a) * f i₀ = a • f i₀ by
        simp [Algebra.smul_def]]
      rw [PiTensorProduct.smul_tprodCoeff]
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod]
      simp
    change r • (PiTensorProduct.tprod ℚ_[p])
        (Function.update f i₀ ((algebraMap ℚ_[p] (P.Factor i₀) a) * f i₀)) =
      a • r • (PiTensorProduct.tprod ℚ_[p]) f
    rw [hscale]
    exact smul_comm r a ((PiTensorProduct.tprod ℚ_[p]) f)
  · intro x y hx hy
    simp only [map_add, smul_add, hx, hy]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
