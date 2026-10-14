import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Semilinear

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-RECOGNITION
source: the standard homogeneous continuous cochain complex in degree one.
fidelity: every standard H1 class has a continuous crossed-homomorphism
representative. Equality of these classes is equivalent to an actual
coboundary equation. The proofs use the actual homology cokernel.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.ContinuousH1Recognition
open CategoryTheory TopRep ContRepresentation ContinuousH1Homogeneous
open scoped Topology
universe u v
noncomputable section
variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{v} R G)

private theorem cycles_i_injective : Function.Injective ((homogeneousCochains X).iCycles 1) := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (cyclesKerIso X).hom).1
  apply Subtype.ext
  have he : (cyclesKerIso X).hom ≫ TopModuleCat.kerι ((homogeneousCochains X).d 1 2) =
      (homogeneousCochains X).iCycles 1 := by
    dsimp only [cyclesKerIso, Limits.KernelFork.mapIsoOfIsLimit]
    simpa using Limits.KernelFork.mapOfIsLimit_ι
      (Limits.KernelFork.ofι ((homogeneousCochains X).iCycles 1)
        ((homogeneousCochains X).iCycles_d 1 2))
      (TopModuleCat.isLimitKer ((homogeneousCochains X).d 1 2)) (𝟙 _)
  exact (congrArg (fun m => m a) he).trans (hab.trans (congrArg (fun m => m b) he).symm)

theorem cocycle_one (f : C(G, X)) (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    f 1 = 0 := by
  have h : f 1 = f 1 + f 1 := by
    have h := hf 1 1
    have hρ : X.ρ (1 : G) (f 1) = f 1 :=
      congrArg (fun L : X →L[R] X => L (f 1)) (map_one X.ρ)
    rw [mul_one, hρ] at h
    exact h
  exact add_left_cancel (h.symm.trans (add_zero (f 1)).symm)

theorem π_surjective : Function.Surjective (ContinuousCohomology.π X 1) := by
  intro x
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (ContinuousH1Semilinear.boundaryRange X)
    ((ContinuousH1Semilinear.homologyCokerIso X).hom x)
  refine ⟨z, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (ContinuousH1Semilinear.homologyCokerIso X).hom).1
  rw [ContinuousH1Semilinear.homologyCokerIso_π, hz]

def cocycleOfClosed (F : (homogeneousCochains X).X 1)
    (_ : (homogeneousCochains X).d 1 2 F = 0) : C(G, X) := F.1 1

theorem cocycleOfClosed_law (F : (homogeneousCochains X).X 1)
    (hF : (homogeneousCochains X).d 1 2 F = 0) (s t : G) :
    cocycleOfClosed X F hF (s * t) =
      X.ρ s (cocycleOfClosed X F hF t) + cocycleOfClosed X F hF s := by
  have hc := congrArg (fun q : (homogeneousCochains X).X 2 => q.1 1 s (s * t)) hF
  change F.1 s (s * t) - (F.1 1 (s * t) - F.1 1 s) = 0 at hc
  have hi := congrArg (fun q : C(G, C(G, X)) => q s (s * t)) (F.2 s)
  change X.ρ s (F.1 (s⁻¹ * s) (s⁻¹ * (s * t))) = F.1 s (s * t) at hi
  simp only [inv_mul_cancel, inv_mul_cancel_left] at hi
  change F.1 1 (s * t) = X.ρ s (F.1 1 t) + F.1 1 s
  rw [hi]
  exact (eq_sub_iff_add_eq.mp (sub_eq_zero.mp hc)).symm

theorem cochain_cocycleOfClosed (F : (homogeneousCochains X).X 1)
    (hF : (homogeneousCochains X).d 1 2 F = 0) :
    cochain X (cocycleOfClosed X F hF) (cocycleOfClosed_law X F hF) = F := by
  apply Subtype.ext
  ext g h
  have he := congrArg (fun q : (homogeneousCochains X).X 2 => q.1 1 g h) hF
  change F.1 g h - (F.1 1 h - F.1 1 g) = 0 at he
  exact (sub_eq_zero.mp he).symm

theorem classOf_surjective (x : continuousCohomology 1 X) :
    ∃ (f : C(G, X)) (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g), classOf X f hf = x := by
  obtain ⟨z, rfl⟩ := π_surjective X x
  let F := (homogeneousCochains X).iCycles 1 z
  have hF : (homogeneousCochains X).d 1 2 F = 0 :=
    congrArg (fun m => m z) ((homogeneousCochains X).iCycles_d 1 2)
  refine ⟨cocycleOfClosed X F hF, cocycleOfClosed_law X F hF, ?_⟩
  apply congrArg (ContinuousCohomology.π X 1)
  apply cycles_i_injective X
  rw [cycle_i]
  exact cochain_cocycleOfClosed X F hF

theorem cocycle_zero_law (s t : G) :
    (0 : C(G, X)) (s * t) = X.ρ s ((0 : C(G, X)) t) + (0 : C(G, X)) s := by
  change (0 : X) = X.ρ s 0 + 0
  rw [map_zero, add_zero]

theorem classOf_zero : classOf X (0 : C(G, X)) (cocycle_zero_law X) = 0 := by
  have hz : cycle X (0 : C(G, X)) (cocycle_zero_law X) = 0 := by
    apply cycles_i_injective X
    rw [cycle_i, map_zero]
    apply Subtype.ext
    ext g h
    exact sub_self 0
  change ContinuousCohomology.π X 1 (cycle X 0 _) = 0
  rw [hz, map_zero]

theorem classOf_eq_zero_iff (f : C(G, X))
    (hf : ∀ g h, f (g * h) = X.ρ g (f h) + f g) :
    classOf X f hf = 0 ↔ ∃ t : X, ∀ g, f g = X.ρ g t - t := by
  constructor
  · intro h
    have hz : (ContinuousH1Semilinear.boundaryRange X).mkQ (cycle X f hf) = 0 := by
      rw [← ContinuousH1Semilinear.homologyCokerIso_π]
      change (ContinuousH1Semilinear.homologyCokerIso X).hom (classOf X f hf) = 0
      rw [h, map_zero]
    have hm := (Submodule.Quotient.mk_eq_zero (ContinuousH1Semilinear.boundaryRange X)).mp hz
    obtain ⟨b, hb⟩ := hm
    have hi := congrArg ((homogeneousCochains X).iCycles 1) hb
    have hd := congrArg (fun m => m b) ((homogeneousCochains X).toCycles_i 0 1)
    simp only [ConcreteCategory.comp_apply] at hd
    change (homogeneousCochains X).iCycles 1 ((homogeneousCochains X).toCycles 0 1 b) =
      (homogeneousCochains X).iCycles 1 (cycle X f hf) at hi
    rw [hd, cycle_i] at hi
    refine ⟨b.1 1, fun g => ?_⟩
    have he := congrArg (fun q : (homogeneousCochains X).X 1 => q.1 1 g) hi
    change b.1 g - b.1 1 = f g - f 1 at he
    rw [cocycle_one X f hf, sub_zero] at he
    have hc := congrArg (fun q : C(G, X) => q g) (b.2 g)
    change X.ρ g (b.1 (g⁻¹ * g)) = b.1 g at hc
    rw [inv_mul_cancel] at hc
    rw [← he, hc]
  · rintro ⟨t, ht⟩
    have he : (fun g => X.ρ g t) = fun g => f g + t :=
      funext fun g => (eq_sub_iff_add_eq.mp (ht g)).symm
    have hc : Continuous (fun g => X.ρ g t) := by
      rw [he]
      exact f.continuous.add continuous_const
    have h := classOf_eq_of_coboundary X 0 f (cocycle_zero_law X) hf t hc (fun g => by
      change f g - 0 = _
      simpa only [sub_zero] using ht g)
    exact h.symm.trans (classOf_zero X)

theorem cocycle_sub_law (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s) (s t : G) :
    (f - g) (s * t) = X.ρ s ((f - g) t) + (f - g) s := by
  change f (s * t) - g (s * t) = X.ρ s (f t - g t) + (f s - g s)
  rw [hf, hg, map_sub]
  abel

theorem cycle_sub (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s) :
    cycle X (f - g) (cocycle_sub_law X f g hf hg) = cycle X f hf - cycle X g hg := by
  unfold cycle
  rw [← map_sub]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  ext s t
  change (f t - g t) - (f s - g s) = (f t - f s) - (g t - g s)
  abel

theorem classOf_sub (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s) :
    classOf X (f - g) (cocycle_sub_law X f g hf hg) = classOf X f hf - classOf X g hg := by
  unfold classOf
  rw [cycle_sub, map_sub]

theorem classOf_eq_iff (f g : C(G, X))
    (hf : ∀ s t, f (s * t) = X.ρ s (f t) + f s)
    (hg : ∀ s t, g (s * t) = X.ρ s (g t) + g s) :
    classOf X f hf = classOf X g hg ↔ ∃ t : X, ∀ s, g s - f s = X.ρ s t - t := by
  constructor
  · intro h
    have hz : classOf X (g - f) (cocycle_sub_law X g f hg hf) = 0 := by
      rw [classOf_sub X g f hg hf, h, sub_self]
    exact (classOf_eq_zero_iff X _ _).mp hz
  · intro h
    have hz := (classOf_eq_zero_iff X (g - f) (cocycle_sub_law X g f hg hf)).mpr h
    rw [classOf_sub X g f hg hf] at hz
    exact (sub_eq_zero.mp hz).symm

end
end JoshiTeich.Act1Scene1.ContinuousH1Recognition
