/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/SubfieldGalois.lean`
original-author: Christian Merten <lana@merten.dev> (Git author; no author header)
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `1314bc8d47c13db19b895144391571f1ac5ecfab`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f` (pi1 package)
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package LICENSE before copying. The source has no
copyright header and the package has no NOTICE file. Retain the license text.
additional-source: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/Morphisms.lean`,
ramificationIdx_comp, commit `1f25e071d914830f6bf691510bbbc23584d1ce80`
(same Git author, coauthor, package snapshot and license; no source copyright header).
modifications: use the local actual normalization inclusions and Galois proof.
Extract the inertia cardinality and ramification-one comparison. Keep default budgets.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationGalois
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Flat.TorsionFree

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Pi1/Orbicurve/SubfieldGalois.lean, ramificationIdx_eq_one_iff.
fidelity: ramification of the actual normalization inclusion is one exactly when
the actual relative inertia fixes the upper intermediate field.
boundary: Scene1/Derived. This supplies the ramification comparison. It assumes
only the stated finite Galois field extension, not an orbicurve covering law.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section

lemma ramificationIdx_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain B] (g : A →+* B) (f : B →+* C) [IsDomain C]
    (hf : Function.Injective f) (w : Ideal C) :
    (letI := (f.comp g).toAlgebra; w.ramificationIdx A) =
      (letI := g.toAlgebra; (w.comap f).ramificationIdx A) *
        (letI := f.toAlgebra; w.ramificationIdx B) := by
  letI := g.toAlgebra
  letI := f.toAlgebra
  letI := (f.comp g).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : (w.comap f).LiesOver (w.comap f) := ⟨rfl⟩
  have : w.LiesOver (w.comap f) := ⟨rfl⟩
  have : Module.IsTorsionFree B C := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hf
  exact Ideal.ramificationIdx_tower (R := A) (S := B) (T := C) (w.comap f) w

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
variable {N F : IntermediateField (rationalBase k t) Ω}
  [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N]
attribute [local instance] galoisNormalizationCoeffComm fieldRingAction
variable (ht : Transcendental k t)

omit [CharZero k] [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N] in
/-- Lift a closed prime along the actual integral normalization inclusion. -/
theorem normalization_exists_maximal_over (hFN : F ≤ N)
    (w : Ideal (coordRing t F)) (hw : w.IsMaximal) :
    ∃ u : Ideal (coordRing t N), u.IsMaximal ∧ u.comap (ringMap hFN) = w := by
  letI iR := ringMapAlgebra hFN
  letI : SMul (coordRing t F) (coordRing t N) := iR.toSMul
  have : w.IsMaximal := hw
  have : Algebra.IsIntegral (coordRing t F) (coordRing t N) := ⟨ringMap_isIntegral hFN⟩
  have : FaithfulSMul (coordRing t F) (coordRing t N) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ringMap_injective hFN)
  obtain ⟨u, hu, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := coordRing t F) (S := coordRing t N) w
  exact ⟨u, hu, hl.over.symm⟩

include ht in
/-- **`e(u | v) = |I_u(N / F)|`**. -/
theorem ramificationIdx_eq_card_inertia (hFN : F ≤ N) (u : Ideal (coordRing t N))
    [hu : u.IsMaximal] :
    letI := ringMapAlgebra hFN
    u.ramificationIdx (coordRing t F) =
      Nat.card ((u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N F : Subgroup _) := by
  letI iR := ringMapAlgebra hFN
  letI : SMul (coordRing t F) (coordRing t N) := iR.toSMul
  letI : Module (coordRing t F) (coordRing t N) := iR.toModule
  haveI : FiniteDimensional (rationalBase k t) F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFN).toLinearMap
      (IntermediateField.inclusion hFN).injective
  haveI : Algebra.IsSeparable (rationalBase k t) F :=
    Algebra.IsSeparable.of_algHom (F := rationalBase k t) (E := F) (E' := N) (IntermediateField.inclusion hFN)
  haveI := normalizationGaloisGroup_fixSub hFN ht
  haveI := moduleFinite_ringMap ht hFN
  haveI := dedekindRing t ht F
  haveI := dedekindRing t ht N
  haveI : Module.IsTorsionFree (coordRing t F) (coordRing t N) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact ringMap_injective hFN
  haveI : Finite (fixSub N F) := inferInstance
  let v := u.comap (algebraMap (coordRing t F) (coordRing t N))
  haveI : v.IsPrime := Ideal.comap_isPrime _ _
  haveI : u.LiesOver v := ⟨rfl⟩
  haveI : CharZero (coordRing t F) :=
    charZero_of_injective_algebraMap (algebraMap k (coordRing t F)).injective
  haveI : CharZero v.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap k v.ResidueField).injective
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v u (fixSub N F),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := fixSub N F) v u]
  change Nat.card (u.toAddSubgroup.inertia (fixSub N F)) = _
  rw [← AddSubgroup.inertia_map_subtype,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

include ht in
/-- Positivity from the actual integral inclusion and the upper Dedekind ring. -/
lemma normalization_ramificationIdx_pos (hFN : F ≤ N) (u : Ideal (coordRing t N))
    [u.IsMaximal] :
    0 < (letI := ringMapAlgebra hFN; u.ramificationIdx (coordRing t F)) := by
  letI := ringMapAlgebra hFN
  have : Algebra.IsIntegral (coordRing t F) (coordRing t N) := ⟨ringMap_isIntegral hFN⟩
  have := dedekindRing t ht N
  exact Ideal.ramificationIdx_pos (coordRing t F) u

include ht in
/-- **Unramifiedness via inertia**: for `F ⊆ L ⊆ N` and a maximal ideal `u` of the coordinate ring
of `N`, `e(u ∩ L | u ∩ F) = 1` iff the inertia group `I_u(N / F)` fixes `L`. -/
theorem ramificationIdx_eq_one_iff {L : IntermediateField (rationalBase k t) Ω} (hFL : F ≤ L) (hLN : L ≤ N)
    (u : Ideal (coordRing t N)) [hu : u.IsMaximal] :
    (letI := ringMapAlgebra hFL; (u.comap (ringMap hLN)).ramificationIdx (coordRing t F)) = 1 ↔
      ((u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N F : Subgroup _) ≤ fixSub N L := by
  have hFN := hFL.trans hLN
  have hcomp : (ringMap hLN).toRingHom.comp (ringMap hFL).toRingHom =
      (ringMap hFN).toRingHom := RingHom.ext fun _ => rfl
  haveI : FiniteDimensional (rationalBase k t) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLN).toLinearMap
      (IntermediateField.inclusion hLN).injective
  haveI : Algebra.IsSeparable (rationalBase k t) L :=
    Algebra.IsSeparable.of_algHom (F := rationalBase k t) (E := L) (E' := N) (IntermediateField.inclusion hLN)
  haveI := dedekindRing t ht L
  have htower := ramificationIdx_comp (ringMap hFL).toRingHom
    (ringMap hLN).toRingHom (ringMap_injective hLN) u
  rw [hcomp] at htower
  have hF := ramificationIdx_eq_card_inertia ht hFN u
  have hL := ramificationIdx_eq_card_inertia ht hLN u
  have hpos := normalization_ramificationIdx_pos ht hLN u
  have hle : ((u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N L : Subgroup _) ≤
      (u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N F := inf_le_inf_left _ (fixSub_antitone hFL)
  constructor
  · intro h1
    change (letI := ringMapAlgebra hFL; (u.comap (ringMap hLN).toRingHom).ramificationIdx
      (coordRing t F)) = 1 at h1
    rw [h1, one_mul] at htower
    have hcard : Nat.card ((u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N F : Subgroup _) =
        Nat.card ((u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N L : Subgroup _) := by
      rw [← hF, ← hL]; exact htower
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
    rw [← heq]
    exact inf_le_right
  · intro h
    have heq : ((u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N F : Subgroup _) =
        (u.inertia (N ≃ₐ[rationalBase k t] N)) ⊓ fixSub N L :=
      le_antisymm (le_inf inf_le_left h) hle
    have : (letI := ringMapAlgebra hFN; u.ramificationIdx (coordRing t F)) =
        (letI := ringMapAlgebra hLN; u.ramificationIdx (coordRing t L)) := by
      rw [hF, hL, heq]
    rw [this] at htower
    have key : ∀ a b : ℕ, 0 < b → b = a * b → a = 1 := fun a b hb h =>
      Nat.eq_of_mul_eq_mul_right hb (by rw [one_mul]; exact h.symm)
    exact key _ _ hpos htower


end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
