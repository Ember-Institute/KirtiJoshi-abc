/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Anabelian/Tempered.lean
-/
import TemperedFundamentalGroups.Orbicurve.Orbifold
import Solutions.Source_ReferenceIutGenuineEtaleComparison
import Solutions.Source_ReferenceIutGenuineCore
import Solutions.Source_ReferenceIutTemperedModel

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open JoshiTeich.ReferenceIut.Anabelian (Orbicurve)
open TemperedFundamentalGroups
open scoped Classical

universe u

noncomputable section

/-- The affine orbifold and its comparison with the specified étale fundamental group.
In positive characteristic the comparison is the homomorphism with constant value one. -/
def modelTemperedPresentation {k : Type u} [Field k] (X : Orbicurve k) :
    Σ Y : AffineOrbifold k, {f : Y.etalePi1 →* genuinePi1 X // Continuous f} :=
  if h : CharZero k then
    letI : CharZero k := h
    let e := modelEtalePi1Equiv X
    ⟨modelNormalizationOrbifold X, e.toMulEquiv.toMonoidHom, e.continuous⟩
  else
    ⟨TemperedFundamentalGroups.Orbicurve.orbicurveOrbifold X.E X.level X.M X.pm,
      1, continuous_const⟩

/-- The tempered theory of the same model orbicurves as the genuine étale theory. -/
def genuineTemperedPi1Theory (h27 : CanLift27.{u}) :
    TemperedPi1Theory (genuineEtalePi1Theory h27) where
  tempPi1 X := (modelTemperedPresentation X).1.canonicalTemperedPi1
  tempPi1Group _ := inferInstance
  tempPi1Topology _ := inferInstance
  tempToEtale X :=
    (modelTemperedPresentation X).2.1.comp ((modelTemperedPresentation X).1.temperedToEtale _)
  tempToEtale_continuous X :=
    (modelTemperedPresentation X).2.2.comp
      ((modelTemperedPresentation X).1.continuous_temperedToEtale _)

end

end AbcAdaptation.Reference.Iut.Anabelian
