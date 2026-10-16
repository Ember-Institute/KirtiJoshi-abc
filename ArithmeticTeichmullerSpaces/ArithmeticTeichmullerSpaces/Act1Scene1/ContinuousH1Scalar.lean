import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Linearity

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-SCALAR
source: scalar action on the standard homogeneous continuous cochain complex.
fidelity: the existing crossed-homomorphism class construction preserves
coefficient scalars; no representation or H1 scalar action is replaced.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
open CategoryTheory TopRep
open scoped Topology
universe u v
noncomputable section
variable {k : Type u} [CommRing k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{v} k G)

theorem cocycle_smul_law (r : k) (f : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s) (s t : G) :
    (r • f) (s * t) = X.ρ s ((r • f) t) + (r • f) s := by
  change r • f (s * t) = X.ρ s (r • f t) + r • f s
  rw [hf, smul_add, map_smul]

theorem cycle_smul (r : k) (f : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s) :
    cycle X (r • f) (cocycle_smul_law X r f hf) = r • cycle X f hf := by
  unfold cycle
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  ext s t
  exact (smul_sub r (f t) (f s)).symm

theorem classOf_smul (r : k) (f : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s) :
    classOf X (r • f) (cocycle_smul_law X r f hf) = r • classOf X f hf := by
  unfold classOf
  rw [cycle_smul, map_smul]

end
end JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
