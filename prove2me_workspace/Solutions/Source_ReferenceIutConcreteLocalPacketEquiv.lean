/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Source of the quotient factors: Iut/Concrete/LocalConstruct/Packet.lean
Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
The tensor map follows the construction of
LocalCompletion.Packet.factorTensorMap in LocalCompletionTensorIndeterminacy.
-/
import Solutions.Source_ReferenceIutConcreteLocalPacket
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorOrder

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField
open JoshiTeich.Act1Scene1.LocalCompletion (Packet padicEmb padicAlgebra finite_padicAlgebra)
open scoped TensorProduct

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)
variable (hc : ∀ j, IsOver K p (c j))

/-- The tuple of actual completions when every place of the packet lies over `p`. -/
def genuinePacket : Packet K (p : ℕ) ι where
  place j := finPart K (c j)
  residueChar_eq j := (hc j).residueChar_finPart

local instance genuineFactorAlgebra (j : ι) :
    Algebra ℚ_[p] ((genuinePacket p c hc).Factor j) :=
  padicAlgebra ((genuinePacket p c hc).residueChar_eq j)

local instance genuineFactorFinite (j : ι) :
    Module.Finite ℚ_[p] ((genuinePacket p c hc).Factor j) :=
  finite_padicAlgebra ((genuinePacket p c hc).residueChar_eq j)

/-- The completion identifies with its quotient by the zero ideal as a `ℚ_p`-algebra. -/
def genuineFactorEquiv (j : ι) :
    (genuinePacket p c hc).Factor j ≃ₐ[ℚ_[p]] Factor K p (c j) := by
  let f : (genuinePacket p c hc).Factor j →ₐ[ℚ_[p]] Factor K p (c j) :=
    { toRingHom := factorMk p (c j)
      commutes' := fun r => by
        change factorMk p (c j) (padicEmb (hc j).residueChar_finPart r) = _
        exact (algebraMap_factor_apply_of_isOver p (c j) (hc j) r).symm }
  exact AlgEquiv.ofBijective f ⟨factorMk_injective p (c j) (hc j), factorMk_surjective p (c j)⟩

@[simp] theorem genuineFactorEquiv_apply (j : ι) (x : (genuinePacket p c hc).Factor j) :
    genuineFactorEquiv p c hc j x = factorMk p (c j) x := rfl

@[simp] theorem genuineFactorEquiv_symm_factorMk (j : ι)
    (x : (genuinePacket p c hc).Factor j) :
    (genuineFactorEquiv p c hc j).symm (factorMk p (c j) x) = x :=
  (genuineFactorEquiv p c hc j).symm_apply_apply x

private def genuineTensorMap :
    (genuinePacket p c hc).Tensor →ₐ[ℚ_[p]] Tensor K (.finite p) c :=
  PiTensorProduct.liftAlgHom
    ((PiTensorProduct.tprod ℚ_[p]).compLinearMap fun j =>
      (genuineFactorEquiv p c hc j).toLinearMap)
    (by
      rw [MultilinearMap.compLinearMap_apply, PiTensorProduct.one_def]
      congr 1)
    (by
      intro x y
      simp only [MultilinearMap.compLinearMap_apply, AlgEquiv.toLinearMap_apply,
        PiTensorProduct.tprod_mul_tprod]
      congr 1)

/-- The tensor of actual completions identifies with the uniform tensor at `p`. -/
def genuineTensorEquiv : (genuinePacket p c hc).Tensor ≃ₐ[ℚ_[p]] Tensor K (.finite p) c :=
  AlgEquiv.ofBijective (genuineTensorMap p c hc) (by
    change Function.Bijective (PiTensorProduct.congr (fun j =>
      (genuineFactorEquiv p c hc j).toLinearEquiv))
    exact (PiTensorProduct.congr (fun j => (genuineFactorEquiv p c hc j).toLinearEquiv)).bijective)

@[simp] theorem genuineTensorEquiv_pure (a : ∀ j, (genuinePacket p c hc).Factor j) :
    genuineTensorEquiv p c hc ((genuinePacket p c hc).pure a) =
      PiTensorProduct.tprod ℚ_[p] (fun j => factorMk p (c j) (a j)) := by
  change genuineTensorMap p c hc (PiTensorProduct.tprod ℚ_[p] a) = _
  simp only [genuineTensorMap, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, AlgEquiv.toLinearMap_apply, genuineFactorEquiv_apply]

@[simp] theorem genuineTensorEquiv_symm_tprod (a : ∀ j, Factor K p (c j)) :
    (genuineTensorEquiv p c hc).symm (PiTensorProduct.tprod ℚ_[p] a) =
      (genuinePacket p c hc).pure (fun j => (genuineFactorEquiv p c hc j).symm (a j)) := by
  apply (genuineTensorEquiv p c hc).injective
  rw [AlgEquiv.apply_symm_apply, genuineTensorEquiv_pure]
  congr 1
  funext j
  exact ((genuineFactorEquiv p c hc j).apply_symm_apply (a j)).symm

/-- The algebra equivalence and its inverse are continuous for the coordinate norms. -/
def genuineTensorContinuousLinearEquiv :
    (genuinePacket p c hc).Tensor ≃L[ℚ_[p]] Tensor K (.finite p) c :=
  (genuineTensorEquiv p c hc).toLinearEquiv.toContinuousLinearEquiv

theorem norm_genuineTensorEquiv_le (x : (genuinePacket p c hc).Tensor) :
    ‖genuineTensorEquiv p c hc x‖ ≤
      ‖(genuineTensorContinuousLinearEquiv p c hc).toContinuousLinearMap‖ * ‖x‖ :=
  (genuineTensorContinuousLinearEquiv p c hc).toContinuousLinearMap.le_opNorm x

theorem norm_genuineTensorEquiv_symm_le (x : Tensor K (.finite p) c) :
    ‖(genuineTensorEquiv p c hc).symm x‖ ≤
      ‖(genuineTensorContinuousLinearEquiv p c hc).symm.toContinuousLinearMap‖ * ‖x‖ :=
  (genuineTensorContinuousLinearEquiv p c hc).symm.toContinuousLinearMap.le_opNorm x

end

end AbcAdaptation.Reference.Iut.LocalConstruct
