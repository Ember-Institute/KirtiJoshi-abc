/-
original-paths: refer/iut/Iut/Concrete/LocalConstruct/Integral.lean,
  refer/iut/Iut/Concrete/LocalConstruct/MaximalOrder.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: b76207ab8955e68a7408d5d2a770b75a30c3bebf
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt tensor integral algebra, order multiplication and integral
closure inclusion to actual completion factors. Reuse this project's proved
finite unit lattice. No reference junk quotient, hull or volume field is copied.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorIntegralBasis
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-ORDER-NORMALIZATION
source: actual integral tensor order and its integral closure; IUT IV
Proposition 1.2 as implemented by the reviewed reference files.
fidelity: equips the actual tensor with its commutative algebra, proves the
unit lattice is a finite integral subalgebra, and constructs its inclusion
in the Z_p integral closure. The latter is open and closed; its finiteness,
compactness and paper hull/volume normalization are not assumed here.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open scoped TensorProduct
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance orderFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)

instance tensorCommRing : CommRing P.Tensor :=
  inferInstanceAs (CommRing (⨂[ℚ_[p]] i, P.Factor i))
instance tensorAlgebra : Algebra ℚ_[p] P.Tensor :=
  inferInstanceAs (Algebra ℚ_[p] (⨂[ℚ_[p]] i, P.Factor i))

instance tensorIntegralAlgebra : Algebra ℤ_[p] P.Tensor where
  smul r x := (r : ℚ_[p]) • x
  algebraMap := (algebraMap ℚ_[p] P.Tensor).comp (algebraMap ℤ_[p] ℚ_[p])
  commutes' r x := Algebra.commutes (r : ℚ_[p]) x
  smul_def' r x := Algebra.smul_def (r : ℚ_[p]) x

theorem pure_mul (a b : ∀ i, P.Factor i) :
    P.pure a * P.pure b = P.pure (fun i => a i * b i) :=
  PiTensorProduct.tprod_mul_tprod a b

theorem one_mem_unitLattice : (1 : P.Tensor) ∈ P.unitLattice := by
  change P.pure (fun _ => 1) ∈ P.unitLattice
  exact P.pure_mem_lattice _ _ (fun _ => by simp)

theorem mul_mem_unitLattice {x y : P.Tensor} (hx : x ∈ P.unitLattice)
    (hy : y ∈ P.unitLattice) : x * y ∈ P.unitLattice := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      rw [P.pure_mul]
      apply P.pure_mem_lattice
      intro i
      simp only [Metric.mem_closedBall, dist_zero_right] at ha hb ⊢
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)).trans (by simpa using hb i)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      change P.pure a * ((r : ℚ_[p]) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul r x _ hx =>
    change ((r : ℚ_[p]) • x) * y ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hx

def unitSubalgebra : Subalgebra ℤ_[p] P.Tensor where
  carrier := P.unitLattice
  mul_mem' := P.mul_mem_unitLattice
  one_mem' := P.one_mem_unitLattice
  add_mem' := P.unitLattice.add_mem
  zero_mem' := P.unitLattice.zero_mem
  algebraMap_mem' r := P.unitLattice.smul_mem r P.one_mem_unitLattice

theorem unitSubalgebra_toSubmodule : P.unitSubalgebra.toSubmodule = P.unitLattice := rfl

theorem isIntegral_of_mem_unitLattice {x : P.Tensor} (hx : x ∈ P.unitLattice) :
    IsIntegral ℤ_[p] x := by
  apply IsIntegral.of_mem_of_fg P.unitSubalgebra _ x hx
  rw [P.unitSubalgebra_toSubmodule]
  exact Module.Finite.iff_fg.mp P.unitLattice_module_finite

def normalization : Subalgebra ℤ_[p] P.Tensor := integralClosure ℤ_[p] P.Tensor

theorem unitLattice_le_normalization : P.unitLattice ≤ P.normalization.toSubmodule :=
  fun _ hx => P.isIntegral_of_mem_unitLattice hx

theorem normalization_isOpen : IsOpen (P.normalization : Set P.Tensor) :=
  AddSubgroup.isOpen_of_mem_nhds P.normalization.toSubmodule.toAddSubgroup
    (Filter.mem_of_superset
      ((P.lattice_balls_isOpen (fun _ => 1) (fun _ => zero_lt_one)).mem_nhds
        (P.unitLattice.zero_mem)) P.unitLattice_le_normalization)

theorem normalization_isClosed : IsClosed (P.normalization : Set P.Tensor) :=
  AddSubgroup.isClosed_of_isOpen P.normalization.toSubmodule.toAddSubgroup P.normalization_isOpen

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
