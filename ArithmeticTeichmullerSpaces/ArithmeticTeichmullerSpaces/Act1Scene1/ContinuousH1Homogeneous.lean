import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.Tactic.Abel

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-HOMOGENEOUS
source: the homogeneous continuous cochain complex in Mathlib, degree one.
fidelity: sends continuous crossed homomorphisms to standard continuous
cohomology. A continuous orbit gives a boundary, so cohomologous crossed
homomorphisms give the same class.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
open CategoryTheory TopRep ContRepresentation
open scoped Topology
universe u v
noncomputable section
variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{v} k G)

def homogeneous (f : C(G, X)) : C(G, C(G, X)) :=
  ⟨fun g => f - ContinuousMap.const G (f g),
    continuous_const.sub (ContinuousMap.continuous_const'.comp f.continuous)⟩

theorem homogeneous_apply (f : C(G, X)) (g h : G) :
    homogeneous X f g h = f h - f g := rfl

def cochain (f : C(G, X)) (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    (homogeneousCochains X).X 1 :=
  ⟨homogeneous X f, by
    intro s
    ext g h
    change X.ρ s (f (s⁻¹ * h) - f (s⁻¹ * g)) = f h - f g
    have he (a : G) : X.ρ s (f (s⁻¹ * a)) = f a - f s := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [mul_inv_cancel_left] using (hf s (s⁻¹ * a)).symm
    rw [map_sub, he h, he g]
    abel⟩

theorem cochain_closed (f : C(G, X)) (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    (homogeneousCochains X).d 1 2 (cochain X f hf) = 0 := by
  apply Subtype.ext
  rw [homogeneousCochains.d_apply]
  ext g h j
  change (f j - f h) - ((f j - f g) - (f h - f g)) = 0
  abel

noncomputable abbrev cyclesKerIso :
    (homogeneousCochains X).cycles 1 ≅
      TopModuleCat.ker ((homogeneousCochains X).d 1 2) :=
  Limits.KernelFork.mapIsoOfIsLimit
    ((homogeneousCochains X).cyclesIsKernel 1 2 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

def cycle (f : C(G, X)) (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    ContinuousCohomology.cocycles X 1 :=
  (cyclesKerIso X).inv ⟨cochain X f hf, cochain_closed X f hf⟩

theorem cycle_i (f : C(G, X)) (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    (homogeneousCochains X).iCycles 1 (cycle X f hf) = cochain X f hf := by
  have he : (cyclesKerIso X).inv ≫ (homogeneousCochains X).iCycles 1 =
      TopModuleCat.kerι ((homogeneousCochains X).d 1 2) := by
    dsimp only [cyclesKerIso, Limits.KernelFork.mapIsoOfIsLimit]
    simpa using Limits.KernelFork.mapOfIsLimit_ι
      (Limits.KernelFork.ofι (TopModuleCat.kerι ((homogeneousCochains X).d 1 2))
        (TopModuleCat.kerι_comp _))
      ((homogeneousCochains X).cyclesIsKernel 1 2 (by simp)) (𝟙 _)
  exact congrArg (fun a => a ⟨cochain X f hf, cochain_closed X f hf⟩) he

def classOf (f : C(G, X)) (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    continuousCohomology 1 X :=
  ContinuousCohomology.π X 1 (cycle X f hf)

def orbit (t : X) (ht : Continuous (fun g => X.ρ g t)) : (homogeneousCochains X).X 0 :=
  ⟨⟨fun g => X.ρ g t, ht⟩, by
    intro s
    ext g
    change X.ρ s (X.ρ (s⁻¹ * g) t) = X.ρ g t
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]⟩

private theorem iCycles_injective : Function.Injective ((homogeneousCochains X).iCycles 1) := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (cyclesKerIso X).hom).1
  apply Subtype.ext
  have he : (cyclesKerIso X).hom ≫
      TopModuleCat.kerι ((homogeneousCochains X).d 1 2) =
      (homogeneousCochains X).iCycles 1 := by
    dsimp only [cyclesKerIso, Limits.KernelFork.mapIsoOfIsLimit]
    simpa using Limits.KernelFork.mapOfIsLimit_ι
      (Limits.KernelFork.ofι ((homogeneousCochains X).iCycles 1)
        ((homogeneousCochains X).iCycles_d 1 2))
      (TopModuleCat.isLimitKer ((homogeneousCochains X).d 1 2)) (𝟙 _)
  exact (congrArg (fun m => m a) he).trans (hab.trans (congrArg (fun m => m b) he).symm)

theorem classOf_eq_of_coboundary (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s)
    (t : X) (ht : Continuous (fun s => X.ρ s t))
    (hfg : ∀ s, g s - f s = X.ρ s t - t) : classOf X f hf = classOf X g hg := by
  let L := homogeneousCochains X
  have hb : cycle X g hg - cycle X f hf = L.toCycles 0 1 (orbit X t ht) := by
    apply iCycles_injective X
    rw [map_sub, cycle_i, cycle_i]
    have he := congrArg (fun m => m (orbit X t ht)) (L.toCycles_i 0 1)
    rw [ConcreteCategory.comp_apply] at he
    rw [he]
    apply Subtype.ext
    rw [homogeneousCochains.d_apply]
    ext s r
    change (g r - g s) - (f r - f s) = X.ρ r t - X.ρ s t
    calc
      _ = (g r - f r) - (g s - f s) := by abel
      _ = _ := by rw [hfg r, hfg s]; abel
  apply sub_eq_zero.mp
  change ContinuousCohomology.π X 1 (cycle X f hf) -
    ContinuousCohomology.π X 1 (cycle X g hg) = 0
  rw [← map_sub]
  have hrev : cycle X f hf - cycle X g hg = -(cycle X g hg - cycle X f hf) := by abel
  rw [hrev, hb, map_neg]
  have he := congrArg (fun m => m (orbit X t ht)) (L.toCycles_comp_homologyπ 0 1)
  simpa only [ConcreteCategory.comp_apply, TopModuleCat.hom_zero_apply, neg_eq_zero] using he

end
end JoshiTeich.Act1Scene1.ContinuousH1Homogeneous
