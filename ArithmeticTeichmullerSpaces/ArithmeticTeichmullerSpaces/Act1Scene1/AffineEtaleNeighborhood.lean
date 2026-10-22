import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib's localization open immersions,
`HasRingHomProperty.Spec_iff`, and `Scheme.Hom.opensRange_localizationAway`.
fidelity: realizes an etale localization algebra as an actual affine scheme,
with its open immersion and etale morphism to the base. Their triangle commutes.
boundary: Scene1/Derived. The arithmetic consumer supplies a proved etale
localization from the same normalization inclusion.
-/

namespace JoshiTeich.Act1Scene1.AffineEtaleNeighborhood

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The affine scheme of a concrete one-element localization. -/
def scheme (f : S) : Scheme := Spec (CommRingCat.of (Localization.Away f))

def inclusion (f : S) : scheme f ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away f)))

instance inclusion_isOpenImmersion (f : S) : IsOpenImmersion (inclusion f) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of S) f

theorem inclusion_opensRange (f : S) :
    (inclusion f).opensRange = PrimeSpectrum.basicOpen f :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of S) f

variable [Algebra R S]

def toBase (f : S) : scheme f ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))

theorem toBase_etale (f : S) [Algebra.Etale R (Localization.Away f)] :
    Etale (toBase (R := R) f) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- The two scheme maps come from the same scalar tower. -/
theorem triangle (f : S) :
    inclusion f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = toBase (R := R) f :=
  (Spec.map_comp (CommRingCat.ofHom (algebraMap R S))
    (CommRingCat.ofHom (algebraMap S (Localization.Away f)))).symm.trans
      (congrArg (fun φ : R →+* Localization.Away f => Spec.map (CommRingCat.ofHom φ))
        (IsScalarTower.algebraMap_eq R S (Localization.Away f)).symm)

end
end JoshiTeich.Act1Scene1.AffineEtaleNeighborhood
