import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Recognition
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-MARKED-TRANSPORT
source: Joshi I pr:galois-cohomology-and-teich (1609--1632),
cor:collation-classes (1636--1643); II.5 pr:arith-isom-gal-cohom (1585--1602).
fidelity: a topological group isomorphism and an equivariant continuous
linear coefficient isomorphism induce a continuous linear equivalence of
the original standard continuous H1 spaces. The cocycle formula is proved
on the original homogeneous complexes. No H1 topology is transported.
Original consumer proofs using Mathlib functoriality; no reference copy.
The production of holomorphoid markings and H1_e/BK compatibility is separate.
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Transport
open CategoryTheory TopRep ContRepresentation
open scoped Topology
universe u v
noncomputable section
variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (X : TopRep.{v} R G) (Y : TopRep.{v} R H)

/-- Source and target markings, with the action compatibility made explicit. -/
structure Marking where
  groupIso : H ≃ₜ* G
  coefficientIso : X ≃L[R] Y
  equivariant : ∀ h x, coefficientIso (X.ρ (groupIso h) x) = Y.ρ h (coefficientIso x)

namespace Marking
variable {X Y} (m : Marking X Y)

def symm : Marking Y X where
  groupIso := m.groupIso.symm
  coefficientIso := m.coefficientIso.symm
  equivariant g y := by
    apply m.coefficientIso.injective
    rw [m.coefficientIso.apply_symm_apply]
    have h := m.equivariant (m.groupIso.symm g) (m.coefficientIso.symm y)
    simpa only [m.groupIso.apply_symm_apply, m.coefficientIso.apply_symm_apply] using h.symm

def coefficientHom : res (ContinuousMonoidHom.toContinuousMonoidHom m.groupIso) X ⟶ Y :=
  TopRep.ofHom {
    toContinuousLinearMap := m.coefficientIso.toContinuousLinearMap
    isIntertwining' h := by
      ext x
      exact m.equivariant h x }

def cochain (f : C(G, X)) : C(H, Y) :=
  (⟨m.coefficientIso, m.coefficientIso.continuous⟩ : C(X, Y)).comp
    (f.comp ⟨m.groupIso, m.groupIso.continuous⟩)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem cochain_law (f : C(G, X))
    (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) (g h : H) :
    m.cochain f (g * h) = Y.ρ g (m.cochain f h) + m.cochain f g := by
  change m.coefficientIso (f (m.groupIso (g * h))) = _
  rw [map_mul, hf, map_add, m.equivariant]
  rfl

def map : continuousCohomology 1 X →L[R] continuousCohomology 1 Y :=
  (ContinuousCohomology.map (ContinuousMonoidHom.toContinuousMonoidHom m.groupIso) m.coefficientHom 1).hom

private theorem cycles_i_injective (Z : TopRep.{v} R G) :
    Function.Injective ((homogeneousCochains Z).iCycles 1) := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (ContinuousH1Homogeneous.cyclesKerIso Z).hom).1
  apply Subtype.ext
  have he : (ContinuousH1Homogeneous.cyclesKerIso Z).hom ≫
      TopModuleCat.kerι ((homogeneousCochains Z).d 1 2) = (homogeneousCochains Z).iCycles 1 := by
    dsimp only [ContinuousH1Homogeneous.cyclesKerIso, Limits.KernelFork.mapIsoOfIsLimit]
    simpa using Limits.KernelFork.mapOfIsLimit_ι
      (Limits.KernelFork.ofι ((homogeneousCochains Z).iCycles 1)
        ((homogeneousCochains Z).iCycles_d 1 2))
      (TopModuleCat.isLimitKer ((homogeneousCochains Z).d 1 2)) (𝟙 _)
  exact (congrArg (fun f => f a) he).trans (hab.trans (congrArg (fun f => f b) he).symm)

theorem map_classOf (f : C(G, X))
    (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    m.map (ContinuousH1Homogeneous.classOf X f hf) =
      ContinuousH1Homogeneous.classOf Y (m.cochain f) (m.cochain_law f hf) := by
  have hπ := congrArg (fun a => a (ContinuousH1Homogeneous.cycle X f hf))
    (ContinuousCohomology.π_map (ContinuousMonoidHom.toContinuousMonoidHom m.groupIso) m.coefficientHom 1)
  change m.map (ContinuousH1Homogeneous.classOf X f hf) =
    ContinuousCohomology.π Y 1
      (ContinuousCohomology.cocyclesMap (ContinuousMonoidHom.toContinuousMonoidHom m.groupIso) m.coefficientHom 1
        (ContinuousH1Homogeneous.cycle X f hf)) at hπ
  rw [hπ, ContinuousH1Homogeneous.classOf]
  apply congrArg (ContinuousCohomology.π Y 1)
  apply cycles_i_injective
  have hi := congrArg (fun a => a (ContinuousH1Homogeneous.cycle X f hf))
    (HomologicalComplex.cyclesMap_i
      (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.toContinuousMonoidHom m.groupIso) m.coefficientHom) 1)
  change (homogeneousCochains Y).iCycles 1
    (ContinuousCohomology.cocyclesMap (ContinuousMonoidHom.toContinuousMonoidHom m.groupIso) m.coefficientHom 1
      (ContinuousH1Homogeneous.cycle X f hf)) =
    (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.toContinuousMonoidHom m.groupIso) m.coefficientHom).f 1
      ((homogeneousCochains X).iCycles 1 (ContinuousH1Homogeneous.cycle X f hf)) at hi
  rw [hi, ContinuousH1Homogeneous.cycle_i, ContinuousH1Homogeneous.cycle_i]
  apply Subtype.ext
  ext g h
  change m.coefficientIso (f (m.groupIso h) - f (m.groupIso g)) =
    m.coefficientIso (f (m.groupIso h)) - m.coefficientIso (f (m.groupIso g))
  exact map_sub m.coefficientIso _ _

theorem symm_map_map (x : continuousCohomology 1 X) : m.symm.map (m.map x) = x := by
  obtain ⟨f, hf, rfl⟩ := ContinuousH1Recognition.classOf_surjective X x
  rw [m.map_classOf, m.symm.map_classOf]
  have he : m.symm.cochain (m.cochain f) = f := by
    ext g
    change m.coefficientIso.symm (m.coefficientIso (f (m.groupIso (m.groupIso.symm g)))) = f g
    rw [m.groupIso.apply_symm_apply, m.coefficientIso.symm_apply_apply]
  congr 1

theorem map_symm_map (y : continuousCohomology 1 Y) : m.map (m.symm.map y) = y := by
  obtain ⟨f, hf, rfl⟩ := ContinuousH1Recognition.classOf_surjective Y y
  rw [m.symm.map_classOf, m.map_classOf]
  have he : m.cochain (m.symm.cochain f) = f := by
    ext h
    change m.coefficientIso (m.coefficientIso.symm (f (m.groupIso.symm (m.groupIso h)))) = f h
    rw [m.groupIso.symm_apply_apply, m.coefficientIso.apply_symm_apply]
  congr 1

def h1Equiv : continuousCohomology 1 X ≃L[R] continuousCohomology 1 Y where
  toFun := m.map
  invFun := m.symm.map
  left_inv := m.symm_map_map
  right_inv := m.map_symm_map
  map_add' := m.map.map_add
  map_smul' := m.map.map_smul
  continuous_toFun := m.map.continuous
  continuous_invFun := m.symm.map.continuous

theorem h1Equiv_classOf (f : C(G, X))
    (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    m.h1Equiv (ContinuousH1Homogeneous.classOf X f hf) =
      ContinuousH1Homogeneous.classOf Y (m.cochain f) (m.cochain_law f hf) := m.map_classOf f hf

end Marking
end
end JoshiTeich.Act1Scene1.ContinuousH1Transport
