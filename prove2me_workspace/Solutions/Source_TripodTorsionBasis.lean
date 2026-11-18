/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/TorsionBasis.lean
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Torsion.Count
import Solutions.Source_TripodTorsionDegree
import Theorems.Thm_AbcAdaptation_Tripod_legendre_isElliptic

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open WeierstrassCurve
open scoped Classical

/-- The `n`-torsion of the Legendre model is finite for `n ≠ 0`. -/
theorem legendre_torsionFinite (l : Qbar) (n : ℕ) (hn : n ≠ 0) : TorsionFinite l n :=
  JoshiTeich.ReferenceIut.Torsion.torsion_finite (W := legendre l) rfl rfl n hn

/-- The prime torsion of a Legendre curve at a tripod point has rank two. -/
theorem legendre_torsionBasis (x : Pt) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point ℓ ≃+ (Fin 2 → ZMod ℓ)) :=
  haveI : (legendre x.1).IsElliptic := legendre_isElliptic x.2.1 x.2.2
  JoshiTeich.ReferenceIut.Torsion.torsionBasis (W := legendre x.1) rfl rfl ℓ

/-- A basis exists for the `3`-torsion at every tripod point. -/
theorem legendre_torsionBasis_three (x : Pt) :
    Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point 3 ≃+ (Fin 2 → ZMod 3)) :=
  legendre_torsionBasis x 3

/-- A basis exists for the `5`-torsion at every tripod point. -/
theorem legendre_torsionBasis_five (x : Pt) :
    Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point 5 ≃+ (Fin 2 → ZMod 5)) :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  legendre_torsionBasis x 5

/-- The `3`-torsion degree bound at every tripod point. -/
theorem torsionDegreeBound_three' : ∀ x : Pt, TorsionDegreeBound x.1 3 :=
  torsionDegreeBound_three_onPt legendre_torsionBasis_three

/-- The `5`-torsion degree bound at every tripod point. -/
theorem torsionDegreeBound_five' : ∀ x : Pt, TorsionDegreeBound x.1 5 :=
  torsionDegreeBound_five_onPt legendre_torsionBasis_five

end AbcAdaptation.Tripod
