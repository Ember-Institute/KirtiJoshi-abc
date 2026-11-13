/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent adaptation of Belyi/CurveField/Divisor.lean at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatRiemannSpaces

set_option autoImplicit false

open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- The actual finite principal divisor, with the source convention div(0)=0. -/
noncomputable def functionDivisor (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) : Divisor M := by
  letI : IsCurveField M.K := M.isCurveField
  exact Finsupp.ofSupportFinite (fun P => ord M hDVR P f)
    (by simpa only [Function.support, ord_eq_placeOrd] using Place.finite_setOf_ord_ne_zero f)

@[simp] theorem functionDivisor_apply (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) (P : Place M.K) : functionDivisor M hDVR f P = ord M hDVR P f := rfl

noncomputable def functionZeroDivisor (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) : Divisor M := by
  letI : IsCurveField M.K := M.isCurveField
  exact Finsupp.ofSupportFinite (fun P => max 0 (ord M hDVR P f))
    ((show {P : Place M.K | ord M hDVR P f ≠ 0}.Finite by
      simpa only [ord_eq_placeOrd] using Place.finite_setOf_ord_ne_zero f).subset
        fun P hP => by
          simp only [Function.mem_support] at hP
          simp only [Set.mem_setOf_eq]
          omega)

noncomputable def functionPoleDivisor (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) : Divisor M := by
  letI : IsCurveField M.K := M.isCurveField
  exact Finsupp.ofSupportFinite (fun P => max 0 (-ord M hDVR P f))
    ((show {P : Place M.K | ord M hDVR P f ≠ 0}.Finite by
      simpa only [ord_eq_placeOrd] using Place.finite_setOf_ord_ne_zero f).subset
        fun P hP => by
          simp only [Function.mem_support] at hP
          simp only [Set.mem_setOf_eq]
          omega)

@[simp] theorem functionZeroDivisor_apply (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) (P : Place M.K) : functionZeroDivisor M hDVR f P = max 0 (ord M hDVR P f) := rfl

@[simp] theorem functionPoleDivisor_apply (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) (P : Place M.K) : functionPoleDivisor M hDVR f P = max 0 (-ord M hDVR P f) := rfl

theorem functionPoleDivisor_nonneg (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) : 0 ≤ functionPoleDivisor M hDVR f := fun P => by simp

theorem functionDivisor_eq_zero_sub_pole (M : Model N) (hDVR : PlacesDiscrete M)
    (f : M.K) : functionDivisor M hDVR f =
      functionZeroDivisor M hDVR f - functionPoleDivisor M hDVR f := by
  ext P
  simp only [functionDivisor_apply, Finsupp.coe_sub, Pi.sub_apply,
    functionZeroDivisor_apply, functionPoleDivisor_apply]
  omega

theorem functionDivisor_of_isAlgebraic (M : Model N) (hDVR : PlacesDiscrete M)
    {f : M.K} (hf : IsAlgebraic ℚ f) : functionDivisor M hDVR f = 0 := by
  letI : IsCurveField M.K := M.isCurveField
  ext P
  simp [ord_eq_placeOrd, P.ord_eq_zero_of_isAlgebraic hf]

@[simp] theorem functionDivisor_one (M : Model N) (hDVR : PlacesDiscrete M) :
    functionDivisor M hDVR 1 = 0 :=
  functionDivisor_of_isAlgebraic M hDVR isAlgebraic_one

theorem divisorDegree_nsmul (M : Model N) (n : ℕ) (A : Divisor M) :
    divisorDegree M (n • A) = n * divisorDegree M A := by
  simpa only [nsmul_eq_mul, divisorDegreeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    using map_nsmul (divisorDegreeHom M) n A

/-- Actual pole correction for an actual basis of M.K over ℚ(u). -/
noncomputable def functionBasis (M : Model N) :
    Module.Basis (Fin (Module.finrank ℚ⟮M.u⟯ M.K)) ℚ⟮M.u⟯ M.K := by
  letI : FiniteDimensional ℚ⟮M.u⟯ M.K := M.finite_u
  exact Module.finBasis ℚ⟮M.u⟯ M.K

noncomputable def basisPoleCorrection (M : Model N) (hDVR : PlacesDiscrete M) : Divisor M :=
  ∑ i, functionPoleDivisor M hDVR (functionBasis M i)

theorem basisPoleCorrection_nonneg (M : Model N) (hDVR : PlacesDiscrete M) :
    0 ≤ basisPoleCorrection M hDVR := fun P => by
  rw [basisPoleCorrection, Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun i _ => functionPoleDivisor_nonneg M hDVR _ P

/-- The source fiber-degree theorem implies the product-formula statement
that every actual principal divisor has degree zero. Constants are handled
as constants; no hypothesis that the constant field equals ℚ is used. -/
theorem principalDegreeZero_of_zeroPoleDegrees
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hFibers : ∀ f : M.K, Transcendental ℚ f →
      divisorDegree M (functionZeroDivisor M hDVR f) =
        (Module.finrank ℚ⟮f⟯ M.K : ℤ) ∧
      divisorDegree M (functionPoleDivisor M hDVR f) =
        (Module.finrank ℚ⟮f⟯ M.K : ℤ))
    (f : M.K) : divisorDegree M (functionDivisor M hDVR f) = 0 := by
  by_cases hf : IsAlgebraic ℚ f
  · rw [functionDivisor_of_isAlgebraic M hDVR hf, divisorDegree_zero]
  · obtain ⟨h0, hPole⟩ := hFibers f hf
    rw [functionDivisor_eq_zero_sub_pole, divisorDegree_sub, h0, hPole, sub_self]

end AbcAdaptation.Tripod.Fermat.Proper
