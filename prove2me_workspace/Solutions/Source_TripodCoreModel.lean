/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Anabelian/Geometry.lean and Iut/Anabelian/Local.lean
-/
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Model
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure
import Solutions.Source_TripodCoreGeometry

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open JoshiTeich.ReferenceIut.Anabelian (Orbicurve EtalePi1Theory)
open WeierstrassCurve
open scoped Classical Valued

universe u

/-- The reference orbicurve model over the chosen étale fundamental group theory. -/
noncomputable def modelAG (Pi1 : EtalePi1Theory.{u}) : AnabelianGeometry.{u} where
  Orbicurve k _ := Orbicurve k
  Cover := Orbicurve.Cover
  coverComp := Orbicurve.Cover.comp
  baseChange f X := X.baseChange f
  coverBaseChange := @fun _ _ _ _ f _ _ c => Orbicurve.Cover.baseChange f c
  oncePunctured E _ := Orbicurve.oncePunctured E
  pmQuotient := Orbicurve.pmQuotient
  pi1 := Pi1.pi1
  pi1Cover := Pi1.pi1Cover
  pi1Cover_continuous := Pi1.pi1Cover_continuous
  pi1Cover_isOpenEmbedding := Pi1.pi1Cover_isOpenEmbedding
  IsCartesianSquare := Orbicurve.IsCartesianSquare
  Cusp := Orbicurve.Cusp
  cuspBaseChange f X c := X.cuspBaseChange f c
  HasCore := Pi1.HasCore
  IsTypeOneEllTors := Orbicurve.IsTypeOneEllTors
  IsTypeOneEllTorsPM := Orbicurve.IsTypeOneEllTorsPM
  TateStructure X := AbcAdaptation.Reference.Iut.TateStructure X.E
  IsTypeOneZModPM ℓ X S := ℓ.Prime ∧ X.level = ℓ ∧ X.M = S.graphLine ℓ ∧ Nat.card X.M = ℓ
  RankOneQuotient X _ := X.Q
  cuspOfQuotient X _ q := X.cuspOf q

theorem modelAG_baseChangeOncePunctured (Pi1 : EtalePi1Theory.{u}) :
    (modelAG Pi1).BaseChangeOncePunctured := by
  intro F K _ _ f E _
  exact Orbicurve.baseChange_oncePunctured f E

theorem modelAG_baseChangePmQuotient (Pi1 : EtalePi1Theory.{u}) :
    (modelAG Pi1).BaseChangePmQuotient := by
  intro F K _ _ f X
  exact Orbicurve.baseChange_pmQuotient f X

theorem modelAG_hasCoreOncePunctured (Pi1 : EtalePi1Theory.{u}) :
    (modelAG Pi1).HasCoreOncePunctured Pi1.excJ := by
  intro F _ _ E _ hj
  exact Pi1.hasCore_oncePunctured E hj

end AbcAdaptation.Reference.Iut.Anabelian

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut.Anabelian
open JoshiTeich.ReferenceIut.Anabelian (EtalePi1Theory)

/-- Core finiteness for the same model and the same curve provider. -/
theorem coreFiniteness_of_modelAG (Pi1 : EtalePi1Theory.{0})
    (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    CoreFinitenessHyp P K d (modelAG Pi1) :=
  coreFiniteness_of_geometry P K d (modelAG Pi1) Pi1.excJ
    (modelAG_baseChangeOncePunctured Pi1) (modelAG_baseChangePmQuotient Pi1)
    (modelAG_hasCoreOncePunctured Pi1)

end AbcAdaptation.Tripod
