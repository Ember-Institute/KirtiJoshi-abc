namespace AbcAdaptation.Reference

section
namespace Iut

universe u v

open NumberField IsDedekindDomain

variable (K : Type u) [Field K] [NumberField K]

noncomputable def inertDeg (w : FinitePlace K) : ℕ :=
  Ideal.inertiaDeg w.maximalIdeal.asIdeal ℤ

end Iut

end

namespace Iut

universe u v

open NumberField WeierstrassCurve TateCurvesTheta

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

def badAll : Set (FinitePlace C.F) := {w | HasMultiplicativeReductionAt C.E w}

structure CurveArithmetic : Prop where

  sqrt_neg_one : IsSquare (-1 : C.F)

  stable_reduction : ∀ w : FinitePlace C.F, HasStableReductionAt C.E w

  six_torsion_rational : SixTorsionRational C.F C.E C.Fbar

  galois_deg_prime : ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → IsGaloisOfDegreePrimeTo C.F C.E ℓ

  exists_liesOver : ∀ w : FinitePlace C.F,
    ∃ v : FinitePlace ↥(fieldOfModuli C.F C.E), FinitePlace.LiesOver w v

  residueChar_liesOver : ∀ (v : FinitePlace ↥(fieldOfModuli C.F C.E)) (w : FinitePlace C.F),
    FinitePlace.LiesOver w v → residueChar w = residueChar v

  mult_invariant : ∀ v : FinitePlace ↥(fieldOfModuli C.F C.E), residueChar v ≠ 2 →
    ∀ w w' : FinitePlace C.F, FinitePlace.LiesOver w v → FinitePlace.LiesOver w' v →
    HasMultiplicativeReductionAt C.E w → HasMultiplicativeReductionAt C.E w'

  badAll_finite : C.badAll.Finite

  inertDeg_pos : ∀ w : FinitePlace C.F, 0 < inertDeg C.F w

  sum_inertDeg_le : ∀ q : ℕ,
    ∑ w ∈ badAll_finite.toFinset.filter (fun w => residueChar w = q), inertDeg C.F w ≤
      Module.finrank ℚ C.F

end EllipticCurveData
end Iut
end AbcAdaptation.Reference
