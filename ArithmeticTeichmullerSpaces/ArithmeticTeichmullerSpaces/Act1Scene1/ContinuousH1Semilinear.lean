import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Homogeneous
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-SEMILINEAR
source: coefficient change in the standard continuous cochain complex.
fidelity: a continuous semilinear equivariant coefficient map induces a
continuous semilinear map on standard H1. It maps closed cochains and
boundaries directly, and uses the actual homology cokernel for descent.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Semilinear
open CategoryTheory TopRep ContRepresentation
open scoped Topology
universe u w v
noncomputable section
variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {S : Type w} [Ring S] [TopologicalSpace S]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {φ : R →+* S} (X : TopRep.{v} R G) (Y : TopRep.{v} S G)

def post {M N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
    [ContinuousSMul R M] [ContinuousSMul S N] (f : M →SL[φ] N) :
    C(G, M) →SL[φ] C(G, N) where
  toFun F := (⟨f, f.continuous⟩ : C(M, N)).comp F
  map_add' F H := by ext g; exact map_add f _ _
  map_smul' r F := by ext g; exact f.map_smulₛₗ r _
  cont := ContinuousMap.continuous_postcomp _

variable (f : X →SL[φ] Y)
variable (hf : ∀ g x, f (X.ρ g x) = Y.ρ g (f x))

def cochainZero : (homogeneousCochains X).X 0 →SL[φ] (homogeneousCochains Y).X 0 where
  toFun F := ⟨post f F.1, by
    intro s
    ext g
    change Y.ρ s (f (F.1 (s⁻¹ * g))) = f (F.1 g)
    rw [← hf]
    exact congrArg f (congrArg (fun t : C(G, X) => t g) (F.2 s))⟩
  map_add' F H := by apply Subtype.ext; ext g; exact map_add f _ _
  map_smul' r F := by apply Subtype.ext; ext g; exact f.map_smulₛₗ r _
  cont := continuous_induced_rng.mpr ((post f).continuous.comp continuous_subtype_val)

def cochainOne : (homogeneousCochains X).X 1 →SL[φ] (homogeneousCochains Y).X 1 where
  toFun F := ⟨post (post f) F.1, by
    intro s
    ext g h
    change Y.ρ s (f (F.1 (s⁻¹ * g) (s⁻¹ * h))) = f (F.1 g h)
    rw [← hf]
    exact congrArg f (congrArg (fun t : C(G, C(G, X)) => t g h) (F.2 s))⟩
  map_add' F H := by apply Subtype.ext; ext g h; exact map_add f _ _
  map_smul' r F := by apply Subtype.ext; ext g h; exact f.map_smulₛₗ r _
  cont := continuous_induced_rng.mpr ((post (post f)).continuous.comp continuous_subtype_val)

theorem map_boundary_cochain (F : (homogeneousCochains X).X 0) :
    cochainOne X Y f hf ((homogeneousCochains X).d 0 1 F) =
      (homogeneousCochains Y).d 0 1 (cochainZero X Y f hf F) := by
  apply Subtype.ext
  change post (post f) (((homogeneousCochains X).d 0 1 F).1) = _
  rw [homogeneousCochains.d_apply, homogeneousCochains.d_apply]
  ext g h
  change f (F.1 h - F.1 g) = f (F.1 h) - f (F.1 g)
  exact map_sub f _ _

theorem map_closed (F : (homogeneousCochains X).X 1)
    (hF : (homogeneousCochains X).d 1 2 F = 0) :
    (homogeneousCochains Y).d 1 2 (cochainOne X Y f hf F) = 0 := by
  apply Subtype.ext
  rw [homogeneousCochains.d_apply]
  ext g h j
  have he := congrArg (fun t : (homogeneousCochains X).X 2 => t.1 g h j) hF
  change F.1 h j - (F.1 g j - F.1 g h) = 0 at he
  change f (F.1 h j) - (f (F.1 g j) - f (F.1 g h)) = 0
  rw [← map_sub, ← map_sub, he, map_zero]

private theorem iso_hom_i (z : ContinuousCohomology.cocycles X 1) :
    ((ContinuousH1Homogeneous.cyclesKerIso X).hom z).1 = (homogeneousCochains X).iCycles 1 z := by
  have he : (ContinuousH1Homogeneous.cyclesKerIso X).hom ≫
      TopModuleCat.kerι ((homogeneousCochains X).d 1 2) = (homogeneousCochains X).iCycles 1 := by
    dsimp only [ContinuousH1Homogeneous.cyclesKerIso, Limits.KernelFork.mapIsoOfIsLimit]
    simpa using Limits.KernelFork.mapOfIsLimit_ι
      (Limits.KernelFork.ofι ((homogeneousCochains X).iCycles 1)
        ((homogeneousCochains X).iCycles_d 1 2))
      (TopModuleCat.isLimitKer ((homogeneousCochains X).d 1 2)) (𝟙 _)
  exact congrArg (fun m => m z) he

private theorem iso_inv_i (z : TopModuleCat.ker ((homogeneousCochains X).d 1 2)) :
    (homogeneousCochains X).iCycles 1 ((ContinuousH1Homogeneous.cyclesKerIso X).inv z) = z.1 := by
  have he : (ContinuousH1Homogeneous.cyclesKerIso X).inv ≫ (homogeneousCochains X).iCycles 1 =
      TopModuleCat.kerι ((homogeneousCochains X).d 1 2) := by
    dsimp only [ContinuousH1Homogeneous.cyclesKerIso, Limits.KernelFork.mapIsoOfIsLimit]
    simpa using Limits.KernelFork.mapOfIsLimit_ι
      (Limits.KernelFork.ofι (TopModuleCat.kerι ((homogeneousCochains X).d 1 2))
        (TopModuleCat.kerι_comp _))
      ((homogeneousCochains X).cyclesIsKernel 1 2 (by simp)) (𝟙 _)
  exact congrArg (fun m => m z) he

private theorem cycles_i_injective : Function.Injective ((homogeneousCochains X).iCycles 1) := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (ContinuousH1Homogeneous.cyclesKerIso X).hom).1
  apply Subtype.ext
  rw [iso_hom_i, iso_hom_i, hab]

def cyclesMap : ContinuousCohomology.cocycles X 1 →SL[φ] ContinuousCohomology.cocycles Y 1 :=
  (ContinuousH1Homogeneous.cyclesKerIso Y).inv.hom.comp
    (((cochainOne X Y f hf).restrict
      (p := ((homogeneousCochains X).d 1 2).hom.ker)
      (q := ((homogeneousCochains Y).d 1 2).hom.ker)
      (fun F hF => map_closed X Y f hf F hF)).comp
      (ContinuousH1Homogeneous.cyclesKerIso X).hom.hom)

theorem cyclesMap_i (z : ContinuousCohomology.cocycles X 1) :
    (homogeneousCochains Y).iCycles 1 (cyclesMap X Y f hf z) =
      cochainOne X Y f hf ((homogeneousCochains X).iCycles 1 z) := by
  change (homogeneousCochains Y).iCycles 1 ((ContinuousH1Homogeneous.cyclesKerIso Y).inv
    ((cochainOne X Y f hf).restrict
      (p := ((homogeneousCochains X).d 1 2).hom.ker)
      (q := ((homogeneousCochains Y).d 1 2).hom.ker)
      (fun F hF => map_closed X Y f hf F hF)
      ((ContinuousH1Homogeneous.cyclesKerIso X).hom z))) = _
  rw [iso_inv_i]
  change cochainOne X Y f hf (((ContinuousH1Homogeneous.cyclesKerIso X).hom z).1) = _
  rw [iso_hom_i]

theorem cyclesMap_boundary (F : (homogeneousCochains X).X 0) :
    cyclesMap X Y f hf ((homogeneousCochains X).toCycles 0 1 F) =
      (homogeneousCochains Y).toCycles 0 1 (cochainZero X Y f hf F) := by
  apply cycles_i_injective Y
  rw [cyclesMap_i]
  have hX := congrArg (fun m => m F) ((homogeneousCochains X).toCycles_i 0 1)
  have hY := congrArg (fun m => m (cochainZero X Y f hf F))
    ((homogeneousCochains Y).toCycles_i 0 1)
  simp only [ConcreteCategory.comp_apply] at hX hY
  rw [hX, map_boundary_cochain, hY]

def cyclesClass : ContinuousCohomology.cocycles X 1 →SL[φ] continuousCohomology 1 Y :=
  (ContinuousCohomology.π Y 1).hom.comp (cyclesMap X Y f hf)

theorem cyclesClass_boundary (F : (homogeneousCochains X).X 0) :
    cyclesClass X Y f hf ((homogeneousCochains X).toCycles 0 1 F) = 0 := by
  change ContinuousCohomology.π Y 1 (cyclesMap X Y f hf _) = 0
  rw [cyclesMap_boundary]
  exact congrArg (fun m => m (cochainZero X Y f hf F))
    ((homogeneousCochains Y).toCycles_comp_homologyπ 0 1)

def boundaryRange : Submodule R (ContinuousCohomology.cocycles X 1) :=
  ((homogeneousCochains X).toCycles 0 1).hom.range

noncomputable abbrev homologyCokerIso : continuousCohomology 1 X ≅
    TopModuleCat.coker ((homogeneousCochains X).toCycles 0 1) :=
  Limits.CokernelCofork.mapIsoOfIsColimit
    ((homogeneousCochains X).homologyIsCokernel 0 1 (by simp))
    (TopModuleCat.isColimitCoker _) (Iso.refl _)

theorem homologyCokerIso_π (z : ContinuousCohomology.cocycles X 1) :
    (homologyCokerIso X).hom (ContinuousCohomology.π X 1 z) = (boundaryRange X).mkQ z := by
  have he : ContinuousCohomology.π X 1 ≫ (homologyCokerIso X).hom =
      TopModuleCat.cokerπ ((homogeneousCochains X).toCycles 0 1) := by
    dsimp only [homologyCokerIso, Limits.CokernelCofork.mapIsoOfIsColimit]
    simpa using Limits.CokernelCofork.π_mapOfIsColimit
      ((homogeneousCochains X).homologyIsCokernel 0 1 (by simp))
      (Limits.CokernelCofork.ofπ (TopModuleCat.cokerπ ((homogeneousCochains X).toCycles 0 1))
        (TopModuleCat.comp_cokerπ _)) (𝟙 _)
  exact congrArg (fun m => m z) he

def quotientMap : (ContinuousCohomology.cocycles X 1 ⧸ boundaryRange X) →SL[φ]
    continuousCohomology 1 Y where
  toLinearMap := (boundaryRange X).liftQ (cyclesClass X Y f hf).toLinearMap (by
    rintro _ ⟨F, rfl⟩
    exact cyclesClass_boundary X Y f hf F)
  cont := Continuous.quotient_lift (cyclesClass X Y f hf).continuous _

def map : continuousCohomology 1 X →SL[φ] continuousCohomology 1 Y :=
  (quotientMap X Y f hf).comp (homologyCokerIso X).hom.hom

theorem map_π (z : ContinuousCohomology.cocycles X 1) :
    map X Y f hf (ContinuousCohomology.π X 1 z) = ContinuousCohomology.π Y 1 (cyclesMap X Y f hf z) := by
  change quotientMap X Y f hf ((homologyCokerIso X).hom (ContinuousCohomology.π X 1 z)) = _
  rw [homologyCokerIso_π]
  rfl

theorem map_classOf (a : C(G, X)) (ha : ∀ g h, a (g * h) = X.ρ g (a h) + a g) :
    map X Y f hf (ContinuousH1Homogeneous.classOf X a ha) =
      ContinuousH1Homogeneous.classOf Y (post f a) (fun g h => by
        change f (a (g * h)) = Y.ρ g (f (a h)) + f (a g)
        rw [ha, map_add, hf]) := by
  rw [ContinuousH1Homogeneous.classOf, map_π]
  apply congrArg (ContinuousCohomology.π Y 1)
  apply cycles_i_injective Y
  rw [cyclesMap_i, ContinuousH1Homogeneous.cycle_i, ContinuousH1Homogeneous.cycle_i]
  apply Subtype.ext
  ext g h
  change f (a h - a g) = f (a h) - f (a g)
  exact map_sub f _ _

end
end JoshiTeich.Act1Scene1.ContinuousH1Semilinear
