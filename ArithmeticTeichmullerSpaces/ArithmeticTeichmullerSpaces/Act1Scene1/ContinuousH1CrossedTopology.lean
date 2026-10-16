import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Recognition

/-!
source-id: JT-SCENE1-CROSSED-COCYCLE-CLASS-CONTINUITY
source: original compact-open continuous cochains and the standard
homogeneous homology quotient.
fidelity: the standard H1 class varies continuously with a continuous
crossed-homomorphism representative, with its inherited cochain topology.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
open CategoryTheory TopRep ContRepresentation
universe u v
noncomputable section
variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{v} R G)

abbrev Crossed := {f : C(G, X) // ∀ g h, f (g * h) = X.ρ g (f h) + f g}

theorem continuous_homogeneous : Continuous (homogeneous X) := by
  let c : C(X, C(G, X)) := ⟨fun x => ContinuousMap.const G x, ContinuousMap.continuous_const'⟩
  have he : homogeneous X = fun f : C(G, X) => ContinuousMap.const G f - c.comp f := by
    funext f
    ext g h
    rfl
  rw [he]
  exact ContinuousMap.continuous_const'.sub (ContinuousMap.continuous_postcomp c)

theorem continuous_crossed_class :
    Continuous (fun f : Crossed X => classOf X f.1 f.2) := by
  have hc : Continuous (fun f : Crossed X => cochain X f.1 f.2) :=
    continuous_induced_rng.mpr ((continuous_homogeneous X).comp continuous_subtype_val)
  have hk : Continuous (fun f : Crossed X =>
      (⟨cochain X f.1 f.2, cochain_closed X f.1 f.2⟩ :
        TopModuleCat.ker ((homogeneousCochains X).d 1 2))) :=
    continuous_induced_rng.mpr hc
  exact (ContinuousCohomology.π X 1).hom.continuous.comp
    ((cyclesKerIso X).inv.hom.continuous.comp hk)

end
end JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
