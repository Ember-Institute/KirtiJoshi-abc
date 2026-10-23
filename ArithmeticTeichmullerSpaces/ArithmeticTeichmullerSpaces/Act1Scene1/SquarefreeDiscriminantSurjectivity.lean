import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.NormTrace

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib discriminant under basis change,
fraction-field localization, and finite torsion-free modules over a PID.
fidelity: an inclusion of finite orders with a common fraction field is
surjective if the smaller order has a squarefree basis discriminant.
boundary: Scene1/Derived. The actual coordinate-ring consumer proves the
squarefree discriminant and supplies the original fraction-field embeddings.
-/

namespace JoshiTeich.Act1Scene1.SquarefreeDiscriminantSurjectivity

open Module Matrix
open scoped Classical nonZeroDivisors
noncomputable section
variable {R A B L : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing A] [IsDomain A] [Algebra R A] [CommRing B] [IsDomain B] [Algebra R B]
  [Field L] [Algebra R L] [Algebra A L] [Algebra B L]
  [IsScalarTower R A L] [IsScalarTower R B L]
  [IsFractionRing A L] [IsFractionRing B L] [FaithfulSMul R L]
  [Module.Finite R B]
variable (f : A →ₐ[R] B) (hf : ∀ a, algebraMap B L (f a) = algebraMap A L a)

include hf in
theorem trace_map [Module.Free R A] [Module.Finite R A] [Module.Free R B]
    (a : A) : Algebra.trace R B (f a) = Algebra.trace R A a := by
  letI : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (fun x y h =>
      (FaithfulSMul.algebraMap_injective R L) (by
        simpa only [IsScalarTower.algebraMap_apply R A L] using congrArg (algebraMap A L) h))
  letI : FaithfulSMul R B :=
    (faithfulSMul_iff_algebraMap_injective R B).mpr (fun x y h =>
      (FaithfulSMul.algebraMap_injective R L) (by
        simpa only [IsScalarTower.algebraMap_apply R B L] using congrArg (algebraMap B L) h))
  letI := FractionRing.liftAlgebra R L
  have := FractionRing.isScalarTower_liftAlgebra (R := R) (K := L)
  apply IsFractionRing.injective R (FractionRing R)
  rw [← Algebra.trace_localization R R⁰ (Rₘ := FractionRing R) (Sₘ := L) (f a), hf,
    Algebra.trace_localization R R⁰ (Rₘ := FractionRing R) (Sₘ := L) a]

include hf in
theorem surjective (n : ℕ) (b : Basis (Fin n) R A)
    (hsq : Squarefree (Algebra.discr R b)) : Function.Surjective f := by
  have : Module.Free R A := .of_basis b
  have : Module.Finite R A := .of_basis b
  have : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (fun x y h => (FaithfulSMul.algebraMap_injective R L) (by
      simpa only [IsScalarTower.algebraMap_apply R B L] using congrArg (algebraMap B L) h))
  have : Module.Free R B := inferInstance
  have hrank : Module.finrank R B = n :=
    (IsFractionRing.finrank_left_eq R B L).trans
      ((IsFractionRing.finrank_left_eq R A L).symm.trans
        ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin n)))
  let c := Module.finBasisOfFinrankEq R B hrank
  let v : Fin n → B := fun i => f (b i)
  have hd : Algebra.discr R v = Algebra.discr R b := by
    unfold Algebra.discr
    congr 1
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, ← map_mul]
    exact trace_map f hf _
  have hindex : (c.toMatrix v).det ^ 2 ∣ Algebra.discr R b := by
    refine ⟨Algebra.discr R c, ?_⟩
    rw [← hd, ← Algebra.discr_of_matrix_vecMul, c.toMatrix_map_vecMul]
  have hu : IsUnit (c.det v) := hsq _ (by simpa only [Basis.det_apply, pow_two] using hindex)
  have hspan : Submodule.span R (Set.range v) = ⊤ := (c.is_basis_iff_det.mpr hu).2
  intro z
  have hz : z ∈ Submodule.span R (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hz
  exact ⟨∑ i, a i • b i, by simpa only [map_sum, map_smul] using ha⟩

end
end JoshiTeich.Act1Scene1.SquarefreeDiscriminantSurjectivity
