import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Homogeneous

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-LINEARITY
source: the additive structure of the homogeneous continuous cochain complex.
fidelity: proves that the explicit crossed-homomorphism-to-H1 construction
preserves addition. The proof uses the same standard continuous complex.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
open CategoryTheory TopRep
open scoped Topology
universe u v
noncomputable section
variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{v} k G)

theorem cocycle_add_law (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s) (s t : G) :
    (f + g) (s * t) = X.ρ s ((f + g) t) + (f + g) s := by
  change f (s * t) + g (s * t) = X.ρ s (f t + g t) + (f s + g s)
  rw [hf, hg, map_add]
  abel

theorem cycle_add (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s) :
    cycle X (f + g) (cocycle_add_law X f g hf hg) = cycle X f hf + cycle X g hg := by
  unfold cycle
  rw [← map_add]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  ext s t
  change (f t + g t) - (f s + g s) = (f t - f s) + (g t - g s)
  abel

theorem classOf_add (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s) :
    classOf X (f + g) (cocycle_add_law X f g hf hg) = classOf X f hf + classOf X g hg := by
  unfold classOf
  rw [cycle_add, map_add]

end
end JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
