import Lean
import Definitions.Def_FermatCurveFieldUniformizer
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_irreducible_valuation_lt_one
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_valuation_aeval_derivative_eq_one
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_succ_mul_derivAlong_not_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_eq_div
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem_integralClosure
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_exists_pow_mul_derivAlong_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_mem
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_unit_mul_pow
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_eq_unit_mul_pow_of_aeval
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRegularRamifiedDerivNotMem
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}


theorem PlatformType_0 (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K}
    (hx : x ∈ O) {p : ℚ[X]} (hp : p ≠ 0) (hv : O.valuation (aeval x p) < 1) :
    ∃ q : ℚ[X], Irreducible q ∧ O.valuation (aeval x q) < 1 := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}



theorem PlatformType_1 (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K}
    (hx : x ∈ O) {q : ℚ[X]} (hq : q.Separable) (hv : O.valuation (aeval x q) < 1) :
    O.valuation (aeval x (derivative q)) = 1 := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}
  (ht : Transcendental ℚ π) [Algebra.IsAlgebraic ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr


theorem PlatformType_2 {k : ℕ} {x : K} (hx : x ∈ O)
    (hk : π ^ k * derivAlong π x ∉ O) : ∃ y ∈ O, π ^ (k + 1) * derivAlong π y ∉ O := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}

open scoped IntermediateField.algebraAdjoinAdjoin
set_option quotPrecheck false in
local notation "𝓑" => integralClosure (Algebra.adjoin ℚ ({π} : Set K)) K





variable (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O)
include ht hQ hπO


theorem PlatformType_3 (hπ1 : O.valuation π < 1) {x : K} (hx : x ∈ O) :
    ∃ b s : 𝓑, O.valuation (s : K) = 1 ∧ x = b / s := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}

open scoped IntermediateField.algebraAdjoinAdjoin
set_option quotPrecheck false in
local notation "𝓑" => integralClosure (Algebra.adjoin ℚ ({π} : Set K)) K

variable (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O)
include ht hQ hπO

variable [IsDiscreteValuationRing O] (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr


theorem PlatformType_4 :
    ∃ N : ℕ, ∀ b : 𝓑, π ^ N * derivAlong π b ∈ O := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}

open scoped IntermediateField.algebraAdjoinAdjoin
set_option quotPrecheck false in
local notation "𝓑" => integralClosure (Algebra.adjoin ℚ ({π} : Set K)) K

variable (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O)
include ht hQ hπO

variable [IsDiscreteValuationRing O] (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr


theorem PlatformType_5 :
    ∃ N : ℕ, ∀ x ∈ O, π ^ N * derivAlong π x ∈ O := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] (O : ValuationSubring K)


theorem PlatformType_6 {π : K} (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
    (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
    (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
    [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
    {x : K} (hx : x ∈ O) : derivAlong π x ∈ O := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}
  (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr


theorem PlatformType_7 {u : K} (hu : O.valuation u = 1) (k : ℕ) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π (u * π ^ (k + 1)) = w * π ^ k := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}
  (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr


theorem PlatformType_8 {t : K} (htO : t ∈ O) {m : ℚ[X]}
    (hm : m.Separable) {u : K} (hu : O.valuation u = 1) {e : ℕ} (he : 1 ≤ e)
    (hmt : aeval t m = u * π ^ e) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π t = w * π ^ (e - 1) := by sorry
end

section
set_option autoImplicit false
open Polynomial
open scoped IntermediateField
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


open NoncriticalRegularRamificationSource


/-- Complete source local obstruction for the actual derivation and actual ramification index. -/
theorem PlatformType_9 {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (hψP : ψ ∈ P.1) (hram : 1 < ramIdx M hDVR ψ P) :
    ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1 := by sorry
end

open AbcAdaptation AbcAdaptation.Tripod.Fermat.Proper
/-- OPEN: source local obstruction. At a regular ramified place, the
actual derivative with respect to ψ fails to preserve the actual local ring.
Both local rings and ramification indices are those of the existing model;
no derivation or derivation law is supplied as a hypothesis. -/
theorem ExistingPlatformType {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (hψP : ψ ∈ P.1) (hram : 1 < ramIdx M hDVR ψ P) :
    ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1 := by
  sorry
open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_irreducible_valuation_lt_one
  let c ← getConstInfo `PlatformType_0
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_irreducible_valuation_lt_one
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.valuation_aeval_derivative_eq_one
  let c ← getConstInfo `PlatformType_1
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.valuation_aeval_derivative_eq_one
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_succ_mul_derivAlong_not_mem
  let c ← getConstInfo `PlatformType_2
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_succ_mul_derivAlong_not_mem
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_eq_div
  let c ← getConstInfo `PlatformType_3
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_eq_div
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_mul_derivAlong_mem_integralClosure
  let c ← getConstInfo `PlatformType_4
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_mul_derivAlong_mem_integralClosure
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_mul_derivAlong_mem
  let c ← getConstInfo `PlatformType_5
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.exists_pow_mul_derivAlong_mem
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.derivAlong_mem
  let c ← getConstInfo `PlatformType_6
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.derivAlong_mem
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.derivAlong_unit_mul_pow
  let c ← getConstInfo `PlatformType_7
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.derivAlong_unit_mul_pow
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.derivAlong_eq_unit_mul_pow_of_aeval
  let c ← getConstInfo `PlatformType_8
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv.derivAlong_eq_unit_mul_pow_of_aeval
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem
  let c ← getConstInfo `PlatformType_9
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem
Original: {a.type}
Exported: {c.type}"
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem
  let c ← getConstInfo `ExistingPlatformType
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Existing target differs"
  IO.FS.writeFile ".local/adaptation/regular-ramified-obstruction-sourceproof-20261114/existing-types-equal.json" "true"
