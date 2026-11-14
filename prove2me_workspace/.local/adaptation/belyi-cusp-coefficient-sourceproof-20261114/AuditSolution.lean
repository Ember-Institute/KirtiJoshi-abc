import Definitions.Def_FermatRiemannComposition
import Definitions.Def_FermatFunctionDivisors
import Definitions.Def_FermatProperDivisorHeight
import Definitions.Def_FermatNoncriticalElementarySource

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors; The genl contributors

Independent source-proof adaptation of Belyi/CurveField/CoordRing.lean:38-163
at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source SHA-256: d21848a412ff4da577615f237816c973cbe3dfd0790f0123f8ff3bc5b11eb180.
The original source's finite place set is the support of the actual existing
Divisor M. The existing coordRing and CuspGenerators are preserved exactly.
The cusp specialization also adapts Genl/Curves/BelyiDescent.lean:289-304
at ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf.
Source SHA-256: fab56e0073e8ad10a1cea54552ba10a62df5cef54da2f572136975cffe375596.
This module contains substantial source proofs; it belongs to the local
Solutions/Source layer and is not a platform Definition submission.
See source-consumer.json for source spans and actual consumers.
-/

set_option autoImplicit false
open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper.CuspCoordRingSource

variable {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
variable [IsCurveField M.K]

/-- The existing reduced cusp divisor has exactly its stated coefficients. -/
theorem cuspDivisor_apply (φ : M.K) (hfin : (cusps M hDVR φ).Finite)
    (P : Place M.K) :
    cuspDivisor M hDVR φ hfin P = if P ∈ cusps M hDVR φ then 1 else 0 := by
  classical
  rw [cuspDivisor, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [Set.Finite.mem_toFinset]

end AbcAdaptation.Tripod.Fermat.Proper.CuspCoordRingSource

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source-proof adaptation of
Belyi/CurveField/BelyiRelation.lean:85-139 and RamIdx.lean:218-223 at
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The current integer index and the supplied finite-sum cusp divisor are retained.
Validation receipts and source mappings are recorded with this logical unit.
-/

set_option autoImplicit false

open Polynomial
open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper.BelyiCuspCoefficientSource

/-- Source RamIdx.lean:218: a rational residue specializes the actual
residue-minpoly index, with no additional law about the constant field. -/
theorem ramIdx_of_residue_eq {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    {φ : M.K} {P : Place M.K} (h : φ ∈ P.1) {c : ℚ}
    (hc : P.residue ⟨φ, h⟩ = algebraMap ℚ P.ResidueField c) :
    ramIdx M hDVR φ P = ord M hDVR P (φ - algebraMap ℚ M.K c) := by
  rw [ramIdx, dif_pos h, hc, minpoly.eq_X_sub_C]
  simp

/-- The source four-case coefficient proof on the actual all-place carrier.
The same supplied cusp-finiteness proof occurs on both the input and output. -/
theorem belyiCanonicalCuspCoefficientIdentity_source {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    ∀ P : Place M.K,
      (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
        else -ramIdx M hDVR φ P - 1) + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P (φ * (φ - 1)) := by
  letI : IsCurveField M.K := M.isCurveField
  obtain ⟨ht, hram⟩ := hφ
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental ht
  have hφ1 : φ - 1 ≠ 0 := by
    intro h
    apply ht
    rw [sub_eq_zero.mp h]
    exact isAlgebraic_one
  have hm1 : (-1 : M.K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  intro P
  simp only [poleMultiplicity, ord_eq_placeOrd]
  rw [P.ord_mul hφ0 hφ1]
  by_cases h : φ ∈ P.1
  · have h0 := P.ord_nonneg_of_mem h
    rw [if_pos h, max_eq_left (neg_nonpos.mpr h0)]
    rcases h0.lt_or_eq with hpos | hzero
    · -- A zero of φ: its index is ord φ, and ord (φ - 1) = 0.
      have hord1 : P.ord (φ - 1) = 0 := by
        rw [sub_eq_neg_add, P.ord_add_eq_of_lt hm1 hφ0
          (by rw [Place.ord_neg, Place.ord_one]; exact hpos), Place.ord_neg, Place.ord_one]
      have hpos' : 0 < ord M hDVR P φ := by
        simpa only [ord_eq_placeOrd] using hpos
      have he : ramIdx M hDVR φ P = P.ord φ := by
        simpa only [ord_eq_placeOrd] using
          noncritical_ramIdx_of_positive_order M hDVR φ P hpos'
      have hPcusp : P ∈ cusps M hDVR φ := Or.inl (by
        simpa only [ord_eq_placeOrd] using hpos.ne')
      rw [he, CuspCoordRingSource.cuspDivisor_apply M hDVR φ hfin P,
        if_pos hPcusp, hord1]
      ring
    · by_cases h1 : 0 < P.ord (φ - 1)
      · -- A value-one cusp: its index is ord (φ - 1).
        have h1P : φ - 1 ∈ P.1 := P.mem_of_ord_nonneg h1.le
        have hres0 : P.residue ⟨φ - 1, h1P⟩ = 0 :=
          P.residue_eq_zero_iff.mpr
            ((P.ord_pos_iff_mem_maximalIdeal (a := ⟨φ - 1, h1P⟩) hφ1).mp h1)
        have hres : P.residue ⟨φ, h⟩ = algebraMap ℚ P.ResidueField 1 := by
          have hsplit : (⟨φ, h⟩ : P.1) = ⟨φ - 1, h1P⟩ + 1 := Subtype.ext (by simp)
          rw [hsplit, map_add, hres0, map_one, map_one, zero_add]
        have he : ramIdx M hDVR φ P = P.ord (φ - 1) := by
          simpa only [map_one, ord_eq_placeOrd] using
            ramIdx_of_residue_eq M hDVR h hres
        have hPcusp : P ∈ cusps M hDVR φ := Or.inr (by
          simpa only [ord_eq_placeOrd] using h1)
        rw [he, CuspCoordRingSource.cuspDivisor_apply M hDVR φ hfin P,
          if_pos hPcusp, ← hzero]
        ring
      · -- At a noncusp, positivity and the Belyi condition give index one.
        have hnot : P ∉ cusps M hDVR φ := by
          rintro (h' | h')
          · apply h'
            simpa only [ord_eq_placeOrd] using hzero.symm
          · apply h1
            simpa only [ord_eq_placeOrd] using h'
        have he : ramIdx M hDVR φ P = 1 := by
          have := noncriticalRamificationPositive M hDVR φ ht P
          have := mt (hram P) hnot
          omega
        have hord1 : P.ord (φ - 1) = 0 := by
          have := P.ord_nonneg_of_mem (sub_mem h P.1.one_mem)
          omega
        rw [he, CuspCoordRingSource.cuspDivisor_apply M hDVR φ hfin P,
          if_neg hnot, hord1, ← hzero]
        simp
  · -- A pole: e = -ord φ, ord (φ - 1) = ord φ, both sides are -e.
    have hneg := (P.ord_neg_iff).mpr h
    have hord1 : P.ord (φ - 1) = P.ord φ := by
      rw [sub_eq_add_neg,
        P.ord_add_eq_of_lt hφ0 hm1 (by rw [Place.ord_neg, Place.ord_one]; exact hneg)]
    have he : ramIdx M hDVR φ P = -P.ord φ :=
      NoncriticalElementarySource.ramIdx_of_notMem M hDVR h
    have hPcusp : P ∈ cusps M hDVR φ := Or.inl (by
      simpa only [ord_eq_placeOrd] using hneg.ne)
    rw [if_neg h, max_eq_right (neg_nonneg.mpr hneg.le), he,
      CuspCoordRingSource.cuspDivisor_apply M hDVR φ hfin P,
      if_pos hPcusp, hord1]
    ring

end AbcAdaptation.Tripod.Fermat.Proper.BelyiCuspCoefficientSource

open AbcAdaptation.Tripod.Fermat.Proper

theorem solution {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    ∀ P : Place M.K,
      (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
        else -ramIdx M hDVR φ P - 1) + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P (φ * (φ - 1)) := by
  exact AbcAdaptation.Tripod.Fermat.Proper.BelyiCuspCoefficientSource.belyiCanonicalCuspCoefficientIdentity_source M hDVR hRF φ hφ hfin

theorem PlatformOriginalType {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : IsBelyi M hDVR φ)
    (hfin : (cusps M hDVR φ).Finite) :
    ∀ P : Place M.K,
      (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
        else -ramIdx M hDVR φ P - 1) + cuspDivisor M hDVR φ hfin P =
        poleMultiplicity M hDVR φ P + ord M hDVR P (φ * (φ - 1)) := by
  exact solution M hDVR hRF φ hφ hfin

open Lean
run_meta do
  let a ← getConstInfo `solution
  let e ← getConstInfo `PlatformOriginalType
  unless ← Lean.Meta.isDefEq a.type e.type do throwError "Original platform type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile ".local/adaptation/belyi-cusp-coefficient-sourceproof-20261114/solution-type-axioms.json" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr a.type).pretty),("axioms",toJson (axs.map toString)),("original_type_equal",Json.bool true)]))
