/-
Adaptation provenance: this wrapper selects original accepted AST command spans.
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original source: Iut/Concrete/Existence.lean; Iut/Concrete/LocalTheory.lean
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_EllipticCurveData
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime
import Mathlib.NumberTheory.RamificationInertia.Valuation

namespace AbcAdaptation.Reference

section
namespace Iut

universe u v

open NumberField IsDedekindDomain

variable (K : Type u) [Field K] [NumberField K]

/-- The residue degree `f_w` of the finite place `w` over its residue characteristic. -/
noncomputable def inertDeg (w : FinitePlace K) : ℕ :=
  Ideal.inertiaDeg w.maximalIdeal.asIdeal ℤ

end Iut

end

namespace Iut

universe u v

open NumberField WeierstrassCurve TateCurvesTheta

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

/-- The places of `F` at which `E` has (bad) multiplicative reduction. -/
def badAll : Set (FinitePlace C.F) := {w | HasMultiplicativeReductionAt C.E w}

/-- **The arithmetic of the curve** (IUT IV, Proposition 1.8; the places of `F/F_mod`):
the standard facts about `E/F` consumed by the construction of initial Θ-data. -/
structure CurveArithmetic : Prop where
  /-- `√−1 ∈ F`. -/
  sqrt_neg_one : IsSquare (-1 : C.F)
  /-- `E` has stable reduction at every finite place of `F`. -/
  stable_reduction : ∀ w : FinitePlace C.F, HasStableReductionAt C.E w
  /-- The `6`-torsion of `E` is rational over `F`. -/
  six_torsion_rational : SixTorsionRational C.F C.E C.Fbar
  /-- `F/F_mod` is Galois of degree prime to every prime `ℓ ≥ 7`. -/
  galois_deg_prime : ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → IsGaloisOfDegreePrimeTo C.F C.E ℓ
  /-- Every finite place of `F` lies over a finite place of `F_mod`. -/
  exists_liesOver : ∀ w : FinitePlace C.F,
    ∃ v : FinitePlace ↥(fieldOfModuli C.F C.E), FinitePlace.LiesOver w v
  /-- A place of `F` over a place of `F_mod` has the same residue characteristic. -/
  residueChar_liesOver : ∀ (v : FinitePlace ↥(fieldOfModuli C.F C.E)) (w : FinitePlace C.F),
    FinitePlace.LiesOver w v → residueChar w = residueChar v
  /-- Multiplicative reduction does not depend on the place of `F` over a given place of
  `F_mod` of odd residue characteristic (`E` descends to `F_tpd` up to twist and has
  semistable reduction). -/
  mult_invariant : ∀ v : FinitePlace ↥(fieldOfModuli C.F C.E), residueChar v ≠ 2 →
    ∀ w w' : FinitePlace C.F, FinitePlace.LiesOver w v → FinitePlace.LiesOver w' v →
    HasMultiplicativeReductionAt C.E w → HasMultiplicativeReductionAt C.E w'
  /-- The bad locus is finite. -/
  badAll_finite : C.badAll.Finite
  /-- Residue degrees are positive. -/
  inertDeg_pos : ∀ w : FinitePlace C.F, 0 < inertDeg C.F w
  /-- Over a rational prime, the residue degrees of the bad places sum to at most
  `[F : ℚ]`. -/
  sum_inertDeg_le : ∀ q : ℕ,
    ∑ w ∈ badAll_finite.toFinset.filter (fun w => residueChar w = q), inertDeg C.F w ≤
      Module.finrank ℚ C.F

end EllipticCurveData
end Iut
end AbcAdaptation.Reference
