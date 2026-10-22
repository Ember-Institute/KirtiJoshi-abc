import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Restrict

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib `IsOpenImmersion.lift`,
`Scheme.presieve₀_mem_precoverage_iff`, and source locality of etaleness.
fidelity: a family of open immersions covering an open subset gives a formal
open cover of that open subscheme. Etaleness of its composites proves that
the restricted morphism is etale. The arithmetic consumer supplies the family
and all its hypotheses from the proved normalization neighborhoods.
boundary: Scene1/Derived; this does not construct an orbicurve comparison.
-/

namespace JoshiTeich.Act1Scene1.EtaleOpenRestriction

open CategoryTheory AlgebraicGeometry
universe u v
noncomputable section

/-- The usual Spec open set, exposed as an open subset of the affine scheme. -/
def specOpen {R : Type u} [CommRing R]
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) : (Spec (CommRingCat.of R)).Opens := U

variable {X : Scheme.{u}} (U : X.Opens) {ι : Type v}
variable (V : ι → Scheme.{u}) (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)]
variable (hsub : ∀ i, Set.range (j i) ⊆ U)

def liftToOpen (i : ι) : V i ⟶ U :=
  IsOpenImmersion.lift U.ι (j i) ((Scheme.Opens.range_ι U).symm ▸ hsub i)

theorem liftToOpen_fac (i : ι) : liftToOpen U V j hsub i ≫ U.ι = j i :=
  IsOpenImmersion.lift_fac U.ι (j i) _

instance liftToOpen_isOpenImmersion (i : ι) : IsOpenImmersion (liftToOpen U V j hsub i) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift U.ι (j i)
    ((Scheme.Opens.range_ι U).symm ▸ hsub i)))

theorem liftToOpen_isPullback (i : ι) :
    CategoryTheory.IsPullback (liftToOpen U V j hsub i) (𝟙 (V i)) U.ι (j i) :=
  IsOpenImmersion.isPullback_lift_id (j i) U.ι _

theorem liftToOpen_comp {Y : Scheme.{u}} (f : X ⟶ Y) (i : ι) :
    liftToOpen U V j hsub i ≫ (U.ι ≫ f) = j i ≫ f :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun g : V i ⟶ X => g ≫ f) (liftToOpen_fac U V j hsub i))

variable (hcover : ∀ x : U, ∃ i, x.val ∈ Set.range (j i))

include hcover in
theorem liftToOpen_covers (x : U) : ∃ i, x ∈ Set.range (liftToOpen U V j hsub i) := by
  obtain ⟨i, y, hy⟩ := hcover x
  refine ⟨i, y, ?_⟩
  apply U.ι.isOpenEmbedding.injective
  have h := congrArg (fun f : V i ⟶ X => f y) (liftToOpen_fac U V j hsub i)
  exact h.trans hy

/-- A formal scheme-theoretic open cover of the selected open subscheme. -/
def openCover : U.toScheme.OpenCover where
  I₀ := ι
  X := V
  f := liftToOpen U V j hsub
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨liftToOpen_covers U V j hsub hcover, fun _ => inferInstance⟩

local instance etaleSourceLocality : IsZariskiLocalAtSource (@Etale.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := @RingHom.Etale)

include hsub hcover in
/-- Etale maps on this cover prove etaleness of the actual restriction. -/
theorem restriction_etale {Y : Scheme.{u}} (f : X ⟶ Y)
    (het : ∀ i, Etale (j i ≫ f)) : Etale (U.ι ≫ f) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (openCover U V j hsub hcover)
  intro i
  exact (liftToOpen_comp U V j hsub f i).symm ▸ het i

end
end JoshiTeich.Act1Scene1.EtaleOpenRestriction
