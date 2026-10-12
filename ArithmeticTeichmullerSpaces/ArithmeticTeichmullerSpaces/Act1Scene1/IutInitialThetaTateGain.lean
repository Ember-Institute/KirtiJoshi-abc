/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Tripod/CyclicTate.lean` and
`refer/iut/Iut/Cor312/ThetaData/TateFamily.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `c35ca616ba5ec707d8ef08a781df35fadba16532`,
`76c7866b5bbc4adbd245a30af1a4fd05d32f8c3f`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0
modification: consumes the actual TateFamily graph-line pullback with the local
Scene1 Tate/Vélu gain; no global product formula or height transport is asserted.
-/

import ArithmeticTeichmullerSpaces.Act1Scene1.IutVeluTateGain
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTateFamily
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.BadPlaceNorm

/-!
source-id: IUT-COR312-INITIAL-THETA-TATE-GAIN-CONSUMER
source: local `TateFamily.graphLineAt` and S1.229 `IutCyclicTate.ratio_mul_bound`.
fidelity: the graph-line membership is consumed on the actual curve over the torsion
field at a selected bad place. The conclusion remains completion-valued and keeps the
point pairs and finite subgroup as explicit inputs.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField WeierstrassCurve TateCurvesTheta
open JoshiTeich.ReferenceIut
open JoshiTeich.ReferenceIut.Anabelian
open IutCyclicVelu IutCyclicTate
open scoped Classical Valued

universe u

noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

local instance (priority := 1100) instDecidableEqIntermediateField :
    DecidableEq ↥D.prime.torsionField :=
  fun a b => Classical.propDecidable (a = b)

/-- The actual Tate family graph line is sufficient for the local Vélu gain. -/
theorem iutInitialThetaTateFamily_ratio_mul_bound
    (TF : TateFamily D.E D.prime.torsionField D.prime.ℓ
      (iutVBadOddModSupportPort D))
    (w : FinitePlace ↥D.prime.torsionField)
    (hw : IsBadPlace D.E D.prime.torsionField
      (iutVBadOddModSupportPort D) w)
    (H : AddSubgroup (curveK D.E D.prime.torsionField).toAffine.Point)
    [Fintype H]
    (hcard : Fintype.card H = D.prime.ℓ)
    (hgraph : H ≤ TF.graphLineAt w hw)
    {T₁ R₁ T₂ R₂ : (curveK D.E D.prime.torsionField).toAffine.Point}
    (hT₁0 : T₁ ≠ 0) (hT₁2 : T₁ + T₁ = 0) (hRT₁ : R₁ + R₁ = T₁)
    (hT₂0 : T₂ ≠ 0) (hT₂2 : T₂ + T₂ = 0) (hRT₂ : R₂ + R₂ = T₂)
    (hT : T₁ ≠ T₂) :
    (‖emb D.prime.torsionField w
        (veluRatio H T₁ R₁)‖ *
      ‖emb D.prime.torsionField w
        (veluRatio H T₂ R₂)‖) ^ 4 ≤
      ‖((TF.S w hw).t.q : localCompletion w)‖ ^ (D.prime.ℓ - 1) := by
  have hV : ∀ v ∈ iutVBadOddModSupportPort D, residueChar v ≠ 2 := by
    intro v hv
    exact hv.1
  have h2 : ‖(2 : localCompletion w)‖ = 1 :=
    norm_two_eq_one_of_notMem
      (two_notMem_of_isBadPlace D.E D.prime.torsionField hV hw)
  have hodd : Odd D.prime.ℓ := by
    have hprime := D.prime.ℓ_prime
    exact hprime.odd_of_ne_two (by
      have hfive := D.prime.five_le
      omega)
  apply ratio_mul_bound
    (emb D.prime.torsionField w)
    (TF.S w hw)
    H hodd hcard h2
  · intro Q hQ
    exact hgraph hQ
  · exact hT₁0
  · exact hT₁2
  · exact hRT₁
  · exact hT₂0
  · exact hT₂2
  · exact hRT₂
  · exact hT

end

end JoshiTeich.Act1Scene1
