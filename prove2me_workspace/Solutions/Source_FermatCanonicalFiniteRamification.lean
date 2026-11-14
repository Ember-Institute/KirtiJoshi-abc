/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent coefficient-support adaptation of Belyi/CurveField/Canonical.lean
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, using the actual fixed Fermat u.
The finite ramification premise is the exact specialization of
Belyi/CurveField/RamIdx.lean finite_setOf_one_lt_ramIdx.
-/
import Definitions.Def_FermatProperDivisorHeight
import Definitions.Def_FermatNoncriticalRamificationPositive

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

/-- The exact coefficients already required by CanonicalDivisorData.
The membership test ranges over every proper valuative place, including infinity. -/
noncomputable def canonicalCoordinateCoefficient (M : Model N)
    (hDVR : PlacesDiscrete M) (P : Place M.K) : ℤ := by
  classical
  exact if M.u ∈ P.1 then ramIdx M hDVR M.u P - 1
    else -ramIdx M hDVR M.u P - 1

/-- Source Canonical.lean:44-58, applied directly to the required coefficient
formula. Actual positive ramification indices and actual finite pole support
are already proved in the imported independent local modules. -/
theorem canonicalCoordinateCoefficient_finiteSupport
    (M : Model N) (hDVR : PlacesDiscrete M)
    (hRam : {P : Place M.K | 1 < ramIdx M hDVR M.u P}.Finite) :
    (Function.support (canonicalCoordinateCoefficient M hDVR)).Finite := by
  letI : IsCurveField M.K := M.isCurveField
  refine ((Place.finite_setOf_notMem M.u).union hRam).subset fun P hP => ?_
  change M.u ∉ P.1 ∨ 1 < ramIdx M hDVR M.u P
  by_cases hu : M.u ∈ P.1
  · apply Or.inr
    have hpos := noncriticalRamificationPositive M hDVR M.u M.transcendental_u P
    have hne : ramIdx M hDVR M.u P - 1 ≠ 0 := by
      simpa only [Function.mem_support, canonicalCoordinateCoefficient, if_pos hu] using hP
    omega
  · exact Or.inl hu

/-- The exact finite divisor; no divisor, coefficients, height or degree is
chosen as additional input. -/
noncomputable def coordinateCanonicalDivisor (M : Model N)
    (hDVR : PlacesDiscrete M)
    (hRam : {P : Place M.K | 1 < ramIdx M hDVR M.u P}.Finite) : Divisor M :=
  Finsupp.ofSupportFinite (canonicalCoordinateCoefficient M hDVR)
    (canonicalCoordinateCoefficient_finiteSupport M hDVR hRam)

@[simp] theorem coordinateCanonicalDivisor_apply (M : Model N)
    (hDVR : PlacesDiscrete M)
    (hRam : {P : Place M.K | 1 < ramIdx M hDVR M.u P}.Finite)
    (P : Place M.K) :
    coordinateCanonicalDivisor M hDVR hRam P =
      canonicalCoordinateCoefficient M hDVR P := rfl

/-- This constructs precisely the existing data contract. In particular the
regular and pole formulas hold at every place of the same actual M.K. -/
noncomputable def coordinateCanonicalData (M : Model N)
    (hDVR : PlacesDiscrete M)
    (hRam : {P : Place M.K | 1 < ramIdx M hDVR M.u P}.Finite) :
    CanonicalDivisorData M hDVR where
  D := coordinateCanonicalDivisor M hDVR hRam
  coefficient := fun P => coordinateCanonicalDivisor_apply M hDVR hRam P

/-- The complete original parent type follows from its exact finite
ramification child. hRF remains in both the child and parent interfaces. -/
theorem canonicalDivisorExists_of_finiteCoordinateRamification
    (hFinite : ∀ {n : ℕ} (M : Model n) (hDVR : PlacesDiscrete M),
      ResiduesFinite M → {P : Place M.K | 1 < ramIdx M hDVR M.u P}.Finite)
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M) :
    Nonempty (CanonicalDivisorData M hDVR) :=
  ⟨coordinateCanonicalData M hDVR (hFinite M hDVR hRF)⟩

end AbcAdaptation.Tripod.Fermat.Proper
