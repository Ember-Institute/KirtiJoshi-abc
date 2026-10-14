/-
original-path: refer/iut/Iut/Concrete/LocalConstruct/MaximalOrder.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: b76207ab8955e68a7408d5d2a770b75a30c3bebf
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt formal-unramified tensor proof to actual completion factors;
use the actual finite tensor basis and Mathlib reduced Artinian decomposition.
No reference quotient factors, hull or freely supplied volume laws are copied.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorOrder
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Artinian.Algebra

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-RESIDUE-DECOMPOSITION
source: reviewed reference MaximalOrder formal-unramified/reduced argument;
Joshi III direct-sum field decomposition (3590--3595).
fidelity: proves the actual tensor is reduced and Artinian, and constructs
its finite product decomposition into residue fields as a Q_p-algebra.
This is an algebraic decomposition; residue-field norms, maximal-order
compactness, hull construction and paper volume identities remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open scoped TensorProduct
universe u
noncomputable section

theorem formallyUnramified_piTensor {R : Type*} [CommRing R] {κ : Type*} [Finite κ]
    (A : κ → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FormallyUnramified R (A i)] :
    Algebra.FormallyUnramified R (⨂[R] i, A i) := by
  classical
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g hfg
  refine PiTensorProduct.algHom_ext fun i => ?_
  apply Algebra.FormallyUnramified.comp_injective I hI
  ext x
  exact AlgHom.congr_fun hfg (PiTensorProduct.singleAlgHom i x)

namespace Packet
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance residueFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance residueFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance residueFactorUnramified (i : ι) : Algebra.FormallyUnramified ℚ_[p] (P.Factor i) :=
  Algebra.FormallyUnramified.of_isSeparable ℚ_[p] (P.Factor i)

instance tensorFormallyUnramified : Algebra.FormallyUnramified ℚ_[p] P.Tensor :=
  formallyUnramified_piTensor (fun i => P.Factor i)
instance tensorIsReduced : IsReduced P.Tensor :=
  Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] P.Tensor
instance tensorIsArtinianRing : IsArtinianRing P.Tensor :=
  IsArtinianRing.of_finite ℚ_[p] P.Tensor

def residueDecomposition : P.Tensor ≃ₐ[ℚ_[p]]
    ∀ I : MaximalSpectrum P.Tensor, P.Tensor ⧸ I.asIdeal :=
  (IsArtinianRing.equivPi P.Tensor).restrictScalars ℚ_[p]

theorem residueDecomposition_apply (x : P.Tensor) (I : MaximalSpectrum P.Tensor) :
    P.residueDecomposition x I = Ideal.Quotient.mk I.asIdeal x := rfl

theorem eq_of_forall_residue_eq {x y : P.Tensor}
    (h : ∀ I : MaximalSpectrum P.Tensor,
      Ideal.Quotient.mk I.asIdeal x = Ideal.Quotient.mk I.asIdeal y) : x = y :=
  P.residueDecomposition.injective (funext h)

end Packet
end
end JoshiTeich.Act1Scene1.LocalCompletion
