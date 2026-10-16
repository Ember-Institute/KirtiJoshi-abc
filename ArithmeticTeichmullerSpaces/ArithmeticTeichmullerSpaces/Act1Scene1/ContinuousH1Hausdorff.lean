import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Semilinear
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-HAUSDORFF
source: standard homogeneous continuous cochains and finite-dimensional
closed subspaces over complete nontrivially normed fields.
fidelity: degree-zero evaluation is injective, so boundaries are finite
dimensional and closed. The original standard H1 quotient is Hausdorff.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Hausdorff
open CategoryTheory TopRep ContRepresentation
universe u v
noncomputable section
variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{v} k G) [T2Space X] [FiniteDimensional k X]

/-- Evaluation uses the existing homogeneous invariant cochains. -/
def evalZero : (homogeneousCochains X).X 0 →ₗ[k] X where
  toFun F := F.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalZero_injective : Function.Injective (evalZero X) := by
  have hval (F : (homogeneousCochains X).X 0) (g : G) :
      X.ρ g (F.1 1) = F.1 g := by
    have he := congrArg (fun t : C(G, X) => t g) (F.2 g)
    change X.ρ g (F.1 (g⁻¹ * g)) = F.1 g at he
    simpa only [inv_mul_cancel] using he
  intro F H h
  apply Subtype.ext
  ext g
  rw [← hval F g, ← hval H g]
  exact congrArg (X.ρ g) h

theorem finiteDimensional_zero : FiniteDimensional k ((homogeneousCochains X).X 0) :=
  FiniteDimensional.of_injective (evalZero X) (evalZero_injective X)

theorem t2_cocycles : T2Space (ContinuousCohomology.cocycles X 1) := by
  haveI : T2Space ((homogeneousCochains X).X 1) := by
    change T2Space ↥(_ : Submodule k C(G, C(G, X)))
    infer_instance
  haveI : T2Space (TopModuleCat.ker ((homogeneousCochains X).d 1 2)) := by
    change T2Space ↥(((homogeneousCochains X).d 1 2).hom.ker)
    infer_instance
  exact (ContinuousH1Homogeneous.cyclesKerIso X).toContinuousLinearEquiv.toHomeomorph.symm.t2Space

theorem boundaryRange_isClosed :
    IsClosed (ContinuousH1Semilinear.boundaryRange X : Set (ContinuousCohomology.cocycles X 1)) := by
  haveI := finiteDimensional_zero X
  haveI := t2_cocycles X
  haveI : FiniteDimensional k (ContinuousH1Semilinear.boundaryRange X) :=
    FiniteDimensional.of_surjective
      ((homogeneousCochains X).toCycles 0 1).hom.toLinearMap.rangeRestrict
      (by rintro ⟨_, F, rfl⟩; exact ⟨F, rfl⟩)
  exact (ContinuousH1Semilinear.boundaryRange X).closed_of_finiteDimensional

/-- Hausdorffness of the original homology topology, via its closed boundary quotient. -/
theorem t2_h1 : T2Space (continuousCohomology 1 X) := by
  haveI : IsClosed (ContinuousH1Semilinear.boundaryRange X :
      Set (ContinuousCohomology.cocycles X 1)) := boundaryRange_isClosed X
  haveI : T2Space (TopModuleCat.coker ((homogeneousCochains X).toCycles 0 1)) := by
    change T2Space (ContinuousCohomology.cocycles X 1 ⧸ ContinuousH1Semilinear.boundaryRange X)
    infer_instance
  exact (ContinuousH1Semilinear.homologyCokerIso X).toContinuousLinearEquiv.toHomeomorph.symm.t2Space

end
end JoshiTeich.Act1Scene1.ContinuousH1Hausdorff
