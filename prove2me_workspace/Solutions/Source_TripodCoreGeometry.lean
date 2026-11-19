/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Tripod/Core.lean and Iut/Anabelian/Model.lean
-/
import Solutions.Source_TripodCoreFiniteness

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open WeierstrassCurve NumberField

universe u

/-- The once-punctured curve commutes with base change along field embeddings. -/
def AnabelianGeometry.BaseChangeOncePunctured (AG : AnabelianGeometry.{u}) : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] (f : F →+* K)
    (E : WeierstrassCurve F) [E.IsElliptic],
    AG.baseChange f (AG.oncePunctured E) = AG.oncePunctured (E.map f)

/-- Base change commutes with the sign quotient in the chosen geometry. -/
def AnabelianGeometry.BaseChangePmQuotient (AG : AnabelianGeometry.{u}) : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] (f : F →+* K) (X : AG.Orbicurve F),
    AG.baseChange f (AG.pmQuotient X) = AG.pmQuotient (AG.baseChange f X)

/-- The nonexceptional implication of [CanLift], Proposition 2.7, in the chosen geometry. -/
def AnabelianGeometry.HasCoreOncePunctured (AG : AnabelianGeometry.{u}) (excJ : Finset ℚ) : Prop :=
  ∀ {F : Type u} [Field F] [CharZero F] (E : WeierstrassCurve F) [E.IsElliptic],
    (∀ c ∈ excJ, E.j ≠ (c : F)) →
      AG.HasCore (AG.oncePunctured E) (AG.pmQuotient (AG.oncePunctured E))

/-- Apply the core theorem directly over each extension, using base change of both objects. -/
theorem OrbicurveDataSection.hasCoreUniversally_of_nonexceptionalJ
    (AG : AnabelianGeometry.{u}) (excJ : Finset ℚ)
    (hOnce : AG.BaseChangeOncePunctured) (hPm : AG.BaseChangePmQuotient)
    (hCore : AG.HasCoreOncePunctured excJ)
    {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
    (hj : ∀ c ∈ excJ, E.j ≠ (c : F)) : HasCoreUniversally AG F E := by
  intro K _ _ f
  have hjK : ∀ c ∈ excJ, (E.map f).j ≠ (c : K) := by
    intro c hc h
    rw [WeierstrassCurve.map_j, ← map_ratCast f] at h
    exact hj c hc (f.injective h)
  change AG.HasCore (AG.baseChange f (AG.oncePunctured E))
    (AG.baseChange f (AG.pmQuotient (AG.oncePunctured E)))
  rw [hPm f (AG.oncePunctured E), hOnce f E]
  exact hCore (E.map f) hjK

end AbcAdaptation.Reference.Iut

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut

/-- The provider points failing the universal core condition have exceptional curve j-invariant. -/
theorem exists_excJ_of_not_hasCore
    (P : CurveProviders) (AG : AnabelianGeometry.{0}) (excJ : Finset ℚ)
    (hOnce : AG.BaseChangeOncePunctured) (hPm : AG.BaseChangePmQuotient)
    (hCore : AG.HasCoreOncePunctured excJ) (x : Pt)
    (hx : ¬ OrbicurveDataSection.HasCoreUniversally AG (P.curve x).F (P.curve x).E) :
    ∃ c ∈ excJ, (P.curve x).E.j = (c : (P.curve x).F) := by
  classical
  by_contra hc
  apply hx
  exact OrbicurveDataSection.hasCoreUniversally_of_nonexceptionalJ
    AG excJ hOnce hPm hCore (P.curve x).E (fun c hmem hj => hc ⟨c, hmem, hj⟩)

/-- Supply the core finiteness required by the curve inputs from the three geometry laws. -/
theorem coreFiniteness_of_geometry
    (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (AG : AnabelianGeometry.{0}) (excJ : Finset ℚ)
    (hOnce : AG.BaseChangeOncePunctured) (hPm : AG.BaseChangePmQuotient)
    (hCore : AG.HasCoreOncePunctured excJ) : CoreFinitenessHyp P K d AG :=
  coreFiniteness_of_exceptionalJ P K d AG excJ
    (fun {x} hx => exists_excJ_of_not_hasCore P AG excJ hOnce hPm hCore x hx)

end AbcAdaptation.Tripod
