import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
finite normalization of the selected tensor component in its fraction field.
fidelity: a finite extension inside the same fraction field becomes an
isomorphism after one nonzero denominator is inverted. The proof clears
denominators of module generators and then uses the localization criterion.
boundary: Scene1/Derived. This concerns ordinary affine schemes, and does
not provide the orbicurve cartesian law.
-/

namespace JoshiTeich.Act1Scene1

universe u
noncomputable section

variable {R A K : Type u} [CommRing R] [IsDomain R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [IsFractionRing R K] [Module.Finite R A]

theorem finite_extension_common_denominator
    (hinj : Function.Injective (algebraMap A K)) :
    ∃ d : R, d ≠ 0 ∧ ∀ a : A, ∃ r : R, algebraMap R A r = d • a := by
  let f : A →ₐ[R] K := IsScalarTower.toAlgHom R A K
  let P : Submodule R K := LinearMap.range (Algebra.linearMap R K)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) s f
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun a => ?_⟩
  have ha : a ∈ Submodule.span R (s : Set A) := by rw [hs]; trivial
  have hmem : (d : R) • f a ∈ P := by
    induction ha using Submodule.span_induction with
    | mem a ha => exact hd a ha
    | zero => simpa only [map_zero, smul_zero] using P.zero_mem
    | add a b _ _ ha hb =>
      simpa only [map_add, smul_add] using P.add_mem ha hb
    | smul c a _ ha =>
      simpa only [map_smul, smul_comm (d : R) c] using P.smul_mem c ha
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, hinj ?_⟩
  calc
    algebraMap A K (algebraMap R A r) = algebraMap R K r :=
      (IsScalarTower.algebraMap_apply R A K r).symm
    _ = (d : R) • f a := hr
    _ = algebraMap A K ((d : R) • a) := (map_smul f (d : R) a).symm

theorem finite_extension_exists_awayMap_bijective
    (hinj : Function.Injective (algebraMap A K)) :
    ∃ d : R, d ≠ 0 ∧ Function.Bijective (Localization.awayMap (algebraMap R A) d) := by
  obtain ⟨d, hd, hden⟩ := finite_extension_common_denominator (R := R) hinj
  have hRA : Function.Injective (algebraMap R A) := by
    intro a b hab
    apply IsFractionRing.injective R K
    simpa only [← IsScalarTower.algebraMap_apply R A K] using
      congrArg (algebraMap A K) hab
  refine ⟨d, hd, ?_, ?_⟩
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    refine ⟨0, ?_⟩
    simpa only [pow_zero, one_mul] using hRA (ha.trans (map_zero _).symm)
  · apply Localization.awayMap_surjective_iff.mpr
    intro a
    obtain ⟨r, hr⟩ := hden a
    exact ⟨r, 1, by simpa only [pow_one, Algebra.smul_def] using hr⟩

open CategoryTheory AlgebraicGeometry

theorem finite_extension_exists_basicOpen_iso
    (hinj : Function.Injective (algebraMap A K)) :
    ∃ d : R, d ≠ 0 ∧ IsIso
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ∣_ PrimeSpectrum.basicOpen d) := by
  obtain ⟨d, hd, hbij⟩ := finite_extension_exists_awayMap_bijective (R := R) hinj
  refine ⟨d, hd, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R A)) d)).mpr
      (isIso_SpecMap_iff.mpr hbij)

theorem finite_extension_birationalOver [IsDomain A]
    (hinj : Function.Injective (algebraMap A K)) {Z : Scheme.{u}}
    (g : Spec (CommRingCat.of R) ⟶ Z) :
    Scheme.BirationalOver (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ g) g := by
  obtain ⟨d, hd, hiso⟩ := finite_extension_exists_basicOpen_iso (R := R) hinj
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen d
  have hRA : Function.Injective (algebraMap R A) := by
    intro a b hab
    apply IsFractionRing.injective R K
    simpa only [← IsScalarTower.algebraMap_apply R A K] using
      congrArg (algebraMap A K) hab
  have hU : Dense (U : Set (Spec (CommRingCat.of R))) := by
    apply U.isOpen.dense
    refine ⟨(⊥ : PrimeSpectrum R), ?_⟩
    change d ≠ 0
    exact hd
  have hV : Dense ((f ⁻¹ᵁ U) : Set (Spec (CommRingCat.of A))) := by
    change Dense (PrimeSpectrum.basicOpen (algebraMap R A d) : Set (PrimeSpectrum A))
    apply (PrimeSpectrum.basicOpen (algebraMap R A d)).isOpen.dense
    refine ⟨(⊥ : PrimeSpectrum A), ?_⟩
    simpa [PrimeSpectrum.mem_basicOpen] using
      (show algebraMap R A d ≠ 0 from fun h => hd (hRA (h.trans (map_zero _).symm)))
  letI : IsIso (f ∣_ U) := hiso
  refine ⟨{
    source := f ⁻¹ᵁ U
    dense_source := hV
    target := U
    dense_target := hU
    iso := asIso (f ∣_ U) }, ?_⟩
  change (f ∣_ U) ≫ U.ι ≫ g = (f ⁻¹ᵁ U).ι ≫ (f ≫ g)
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

end
end JoshiTeich.Act1Scene1
