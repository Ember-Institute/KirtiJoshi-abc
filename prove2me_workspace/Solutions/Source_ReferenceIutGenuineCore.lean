/-
Sources:
* lana-agents/pi1, ca7def953193f861a462aa0831eec8f0a31ff69f (Apache-2.0),
  Pi1/Orbicurve/Core.lean and Pi1/Orbicurve/Pullback.lean (isCoreOf_ofSubfield_iff).
* lana-agents/iut, 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8 (Apache-2.0),
  Iut/Anabelian/Genuine/Core.lean and Iut/Anabelian/GenuineEtale.lean.
-/
import Solutions.Source_ReferenceIutCanLiftPresentationPullback
import Solutions.Source_ReferenceIutGenuineNormalizationCover
import Solutions.Source_ReferenceIutGenuinePi1

set_option autoImplicit false

universe u

namespace JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

variable {k : Type u} [Field k] {X Y : AffineOrbicurvePresentation k}

private theorem locBar_iff_of_pullback (f : Cover X Y)
    (pullback : ∀ (V : AffineOrbicurvePresentation k), Cover V Y →
      ∃ T, Nonempty (Cover T V) ∧ Nonempty (Cover T X))
    (W : AffineOrbicurvePresentation k) : LocBar X W ↔ LocBar Y W := by
  constructor
  · rintro ⟨V, ⟨g⟩, h⟩
    exact ⟨V, ⟨g.comp f⟩, h⟩
  · rintro ⟨V, ⟨g⟩, ⟨h⟩⟩
    obtain ⟨T, ⟨a⟩, hX⟩ := pullback V g
    exact ⟨T, hX, ⟨a.comp h⟩⟩

/-- A cover with common-cover pullbacks preserves the class and its terminal objects. -/
theorem isCoreOf_iff_of_pullback (f : Cover X Y)
    (pullback : ∀ (V : AffineOrbicurvePresentation k), Cover V Y →
      ∃ T, Nonempty (Cover T V) ∧ Nonempty (Cover T X))
    (C : AffineOrbicurvePresentation k) : IsCoreOf X C ↔ IsCoreOf Y C := by
  have h W := locBar_iff_of_pullback f pullback W
  exact ⟨fun hc => ⟨(h C).mp hc.1, fun W hw => hc.2 W ((h W).mpr hw)⟩,
    fun hc => ⟨(h C).mpr hc.1, fun W hw => hc.2 W ((h W).mp hw)⟩⟩

end JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

namespace AbcAdaptation.Reference.Iut.Anabelian

open JoshiTeich.Act1Scene1 WeierstrassCurve
open JoshiTeich.ReferenceIut.Anabelian (EtalePi1Theory Orbicurve)
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open FunctionFieldNormalization AffineOrbicurvePresentation
open scoped Classical IntermediateField.algebraAdjoinAdjoin

noncomputable section

private theorem normalizationIsCore_iff_of_cover {k : Type u} [Field k] [CharZero k]
    {X Y : Orbicurve k} (c : Orbicurve.Cover X Y) (C : AffineOrbicurvePresentation k) :
    IsCoreOf (normalizationPresentation X.E X.level X.M X.pm) C ↔
      IsCoreOf (normalizationPresentation Y.E Y.level Y.M Y.pm) C := by
  cases X with | @mk E hE ℓ M pm =>
  cases Y with | @mk E' hE' ℓ' M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  change E = E' at h
  subst h
  let A := normalizationPresentation E ℓ M pm
  let B := normalizationPresentation E ℓ' M' pm'
  let f : Cover A B := normalizationCoverOfModelCover (X := ⟨E, ℓ, M, pm⟩)
    (Y := ⟨E, ℓ', M', pm'⟩) ⟨rfl, n, hn, hmul, hM, hpm⟩
  obtain ⟨hBA, hf⟩ := normalizationCoverOfModelCover_eq_ringMap E hn hmul hM hpm
  letI : IsAlgClosure (xLine E) (Ω E) := ⟨inferInstance, isAlgebraic_xLine E⟩
  exact isCoreOf_iff_of_pullback f
    (pullback_ofSubfield (transcendental_xG E) hBA
      (mB := B.mult) (mB_pos := B.mult_pos) (mB_fin := B.finite_mult)
      (mA := A.mult) (mA_pos := A.mult_pos) (mA_fin := A.finite_mult) f hf) C

/-- A cover of model orbicurves preserves their cores on the actual normalization presentations. -/
theorem normalizationHasCore_iff_of_cover {k : Type u} [Field k] [CharZero k]
    {X Y C : Orbicurve k} (c : Orbicurve.Cover X Y) :
    normalizationHasCore X C ↔ normalizationHasCore Y C := by
  have h := normalizationIsCore_iff_of_cover c (normalizationPresentation C.E C.level C.M C.pm)
  exact ⟨fun ⟨_, hc⟩ => ⟨inferInstance, h.mp hc⟩, fun ⟨_, hc⟩ => ⟨inferInstance, h.mpr hc⟩⟩

/-- The model theory from the inertia quotients and the characteristic-zero CanLift theorem. -/
def genuineEtalePi1Theory (h27 : CanLift27.{u}) : EtalePi1Theory.{u} where
  pi1 := genuinePi1
  pi1Cover := genuinePi1Cover
  pi1Cover_continuous := genuinePi1Cover_continuous
  pi1Cover_isOpenEmbedding := genuinePi1Cover_isOpenEmbedding
  HasCore := normalizationHasCore
  hasCore_iff_of_cover := normalizationHasCore_iff_of_cover
  excJ := canLiftExceptionalJ
  hasCore_oncePunctured := normalizationHasCore_oncePunctured h27

end

end AbcAdaptation.Reference.Iut.Anabelian
