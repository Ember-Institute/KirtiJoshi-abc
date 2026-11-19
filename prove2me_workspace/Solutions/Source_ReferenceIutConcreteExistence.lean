/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/Main.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22
import Solutions.Source_ReferenceIutConcreteLocalEstimate

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

open NumberField

variable {T : Genl.HeightTheory}
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The data bundles produced by the concrete construction. -/
def IsConcrete (X : Corollary312VariantData.{u, v} AG TG) : Prop :=
  ∃ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)
    (QI : QPilotInputs D), X = concreteVariantData D LT TL QI

/-- **Existence of suitable initial Θ-data, concrete form** ((P7) in the proof of
Corollary 2.2): for a point `x` outside the exceptional set and a prime `ℓ ≥ 7` satisfying
(P2), (P3), (P5), (P6), initial Θ-data with prime `ℓ` together with the local-field theory
and local theta data of its `ℓ`-torsion field, the finiteness of its bad locus, the
arithmetic inputs of its tower, and Steps (ii), (iii) of the proof of Theorem 1.10, with
the expected relations to `x`. The curve construction consumes the anabelian existence and the local
inputs on the same fields (IUT I, Definition 3.1(d)–(f); taxis #1469). -/
def ConcreteThetaDataExistence {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d) : Prop :=
  ∀ x (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d), x ∉ I.excCore →
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ v ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv v) →
    (∀ v ∈ (I.localData x hx).bad, (I.localData x hx).p v = ℓ →
      ((I.localData x hx).hv v : ℝ) < Real.sqrt (I.h x)) →
    (∃ v ∈ (I.localData x hx).bad, (I.localData x hx).p v ≠ 2 ∧ (I.localData x hx).p v ≠ ℓ) →
    I.SL2Image x ℓ →
    ∃ (D : InitialThetaData.{u} AG TG) (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)
      (QI : QPilotInputs D), TowerArithmetic D LT TL ∧
      D.ℓ = ℓ ∧ D.dmod ≤ d ∧
      (concreteVariantData.{u, v} D LT TL QI).qPilot.logQ =
        (I.localData x hx).heightOther 2 ℓ ∧
      T.logDiff T.tripod x = logDifferentDeg ↥D.tripodalField ∧
      D.logConductorDeg ≤ T.logCond T.tripod x ∧
      T.logCond T.tripod x ≤ D.logConductorDeg + Real.log (2 * ℓ)

/-- The concrete existence statement provides the general one, with the concrete data
bundles. -/
theorem ConcreteThetaDataExistence.toThetaDataExistence {K : T.CBS} {d : ℕ}
    {I : Corollary22Inputs T K d}
    (ex : ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) I) :
    ThetaDataExistence (IsConcrete.{u, v} (AG := AG) (TG := TG)) I where
  thetaData x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6 := by
    obtain ⟨D, LT, TL, QI, TA, hℓ, hd, hq, hdiff, hc1, hc2⟩ :=
      ex x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6
    have hseven : 7 ≤ D.ℓ := hℓ.symm ▸ hℓ7
    exact ⟨concreteVariantData D LT TL QI, TL.invariants QI, ⟨D, LT, TL, QI, rfl⟩,
      TA.certificate (QI := QI) hseven, ⟨TA.localEstimate (QI := QI)⟩,
      hℓ, hd, hq, hdiff, hc1, hc2⟩

end AbcAdaptation.Reference.Iut
