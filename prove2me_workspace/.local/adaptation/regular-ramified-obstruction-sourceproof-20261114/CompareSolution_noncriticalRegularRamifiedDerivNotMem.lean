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

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Complete source proof transport from pinned Belyi
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Canonical node layout; source statements and proof bodies stay unchanged.
See source-consumer.json and private-owners.json for every source copy.
-/
import Definitions.Def_FermatNoncriticalElementarySource
import Definitions.Def_FermatCurveFieldUniformizer
import Mathlib.RingTheory.Unramified.Field
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_eq_unit_mul_pow_of_aeval

/- Private proof closure from Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_curveDerivationUniqueness.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv


section Extension

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open KaehlerDifferential TensorProduct

omit [Algebra R S] [IsScalarTower R S T] in
private theorem eq_zero_of_formallyUnramified [Algebra.FormallyUnramified S T]
    (D : Derivation R T T) (hD : ∀ s : S, D (algebraMap S T s) = 0) : D = 0 := by
  let D' : Derivation S T T :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun s x => by
        rw [Algebra.smul_def, D.leibniz, hD, smul_zero, add_zero, smul_eq_mul, RingHom.id_apply,
          Algebra.smul_def]
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  ext x
  change D' x = 0
  rw [← D'.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D S T x) 0,
    map_zero]

omit [Algebra R S] [IsScalarTower R S T] in
private theorem ext_of_formallyUnramified [Algebra.FormallyUnramified S T]
    (D₁ D₂ : Derivation R T T) (h : ∀ s : S, D₁ (algebraMap S T s) = D₂ (algebraMap S T s)) :
    D₁ = D₂ := by
  rw [← sub_eq_zero]
  exact eq_zero_of_formallyUnramified (S := S) _ fun s => by simp [h s]

end Extension

variable {K : Type*} [Field K] [CharZero K] {t : K}

@[simp]
private theorem derivAlong_self (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t t = 1 := by
  simpa using derivAlong_aeval ht X

private theorem derivation_ext_of_eq (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K]
    (D₁ D₂ : Derivation ℚ K K) (h : D₁ t = D₂ t) : D₁ = D₂ := by
  have := formallyEtale_adjoin t
  refine ext_of_formallyUnramified (S := Algebra.adjoin ℚ {t}) D₁ D₂ fun s => ?_
  obtain ⟨p, hp⟩ := (Polynomial.algEquivOfTranscendental ℚ t ht).surjective s
  have : algebraMap (Algebra.adjoin ℚ {t}) K s = aeval t p := by
    rw [← hp]; exact coe_algEquivOfTranscendental t ht p
  rw [this, D₁.map_aeval, D₂.map_aeval, h]

private theorem eq_smul_derivAlong (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K]
    (D : Derivation ℚ K K) : D = D t • derivAlong t :=
  derivation_ext_of_eq ht _ _ (by simp [derivAlong_self ht])

private theorem derivAlong_eq_smul (s : K) (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong s = derivAlong s t • derivAlong t :=
  eq_smul_derivAlong ht _

private theorem derivAlong_mul_derivAlong {s : K} (hs : Transcendental ℚ s) [Algebra.IsAlgebraic ℚ⟮s⟯ K]
    (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t s * derivAlong s t = 1 := by
  have := congrArg (· s) (derivAlong_eq_smul s ht)
  simp only [derivAlong_self hs, Derivation.smul_apply, smul_eq_mul] at this
  rw [this, mul_comm]


end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Private proof closure from Definitions/Def_FermatCurveDerivationValuationElementary.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K}


omit [CharZero K] in
private theorem inv_mem_of_valuation_eq_one {u : K} (hu : O.valuation u = 1) : u⁻¹ ∈ O := by
  rw [← O.valuation_le_one_iff, map_inv₀, hu, inv_one]

variable [IsDiscreteValuationRing O] {π : K} (hπO : π ∈ O)
  (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr





end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/- Private proof closure from Definitions/Def_FermatCurveFieldUniformizer.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.Place

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]


@[simp]
private theorem ord_uniformizer (P : Place K) : P.ord P.uniformizer = 1 :=
  Classical.choose_spec P.exists_ord_eq_one

private theorem uniformizer_ne_zero (P : Place K) : P.uniformizer ≠ 0 := by
  intro h
  have := P.ord_uniformizer
  rw [h, ord_zero] at this
  exact zero_ne_one this

end AbcAdaptation.Tripod.Fermat.Proper.Place

/- Private proof closure from Definitions/Def_FermatNoncriticalRegularRamificationSource.lean. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper.NoncriticalRegularRamificationSource

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

private theorem transcendental_of_ord_ne_zero {P : Place K} {π : K} (h : P.ord π ≠ 0) :
    Transcendental ℚ π :=
  fun ha ↦ h (P.ord_eq_zero_of_isAlgebraic ha)

private theorem isUnit_iff_ord_eq_zero (P : Place K) (y : P.1) (hy : (y : K) ≠ 0) :
    IsUnit y ↔ P.ord y = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : P.1) : K) * ((u⁻¹ : P.1ˣ) : P.1) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    have hu0 : (((u⁻¹ : P.1ˣ) : P.1) : K) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
    have := congrArg P.ord h1
    rw [P.ord_mul hy hu0, P.ord_one] at this
    have h2 := P.ord_nonneg_of_mem (u : P.1).2
    have h3 := P.ord_nonneg_of_mem ((u⁻¹ : P.1ˣ) : P.1).2
    omega
  · intro h0
    have hinv : (y : K)⁻¹ ∈ P.1 := ((P.ord_eq_zero_iff hy).mp h0).2
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy)⟩

private theorem irreducible_of_ord_eq_one (P : Place K) {π : K} (hπ : P.ord π = 1) :
    Irreducible (⟨π, P.mem_of_ord_nonneg (by omega)⟩ : P.1) := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  rw [irreducible_iff]
  refine ⟨fun h ↦ ?_, fun a b hab ↦ ?_⟩
  · rw [isUnit_iff_ord_eq_zero P _ hπ0] at h
    change P.ord π = 0 at h
    omega
  · have hab' : π = (a : K) * b := congrArg Subtype.val hab
    have ha0 : (a : K) ≠ 0 := by rintro h0; rw [h0, zero_mul] at hab'; exact hπ0 hab'
    have hb0 : (b : K) ≠ 0 := by rintro h0; rw [h0, mul_zero] at hab'; exact hπ0 hab'
    rw [isUnit_iff_ord_eq_zero P _ ha0, isUnit_iff_ord_eq_zero P _ hb0]
    have := congrArg P.ord hab'
    rw [P.ord_mul ha0 hb0, hπ] at this
    have h2 := P.ord_nonneg_of_mem a.2
    have h3 := P.ord_nonneg_of_mem b.2
    omega

private theorem exists_valuation_aeval_lt_one (P : Place K) :
    ∀ y ∈ P.1, ∃ p : ℚ[X], p ≠ 0 ∧ P.1.valuation (aeval y p) < 1 := by
  intro y hy
  refine ⟨minpoly ℚ (P.residue ⟨y, hy⟩), minpoly.ne_zero (P.noncritical_isIntegral_residue _), ?_⟩
  refine (P.1.valuation_lt_one_iff ⟨_, P.noncritical_aeval_mem hy _⟩).mp ((P.residue_eq_zero_iff).mp ?_)
  rw [P.noncritical_residue_aeval hy]
  exact minpoly.aeval ℚ _

private theorem valuation_eq_one_of_ord_eq_zero (P : Place K) {u : K} (hu0 : u ≠ 0)
    (hu : P.ord u = 0) : P.1.valuation u = 1 := by
  obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff hu0).mp hu
  have := (P.1.valuation_eq_one_iff ⟨u, h1⟩).mp
    ((isUnit_iff_ord_eq_zero P ⟨u, h1⟩ hu0).mpr hu)
  exact this

private theorem ord_eq_zero_of_valuation_eq_one (P : Place K) {w : K} (hw : P.1.valuation w = 1) :
    P.ord w = 0 := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  exact (P.ord_eq_zero_iff hw0).mpr
    ⟨(P.1.valuation_le_one_iff w).mp hw.le, CurveDeriv.inv_mem_of_valuation_eq_one hw⟩


end AbcAdaptation.Tripod.Fermat.Proper.NoncriticalRegularRamificationSource

/- Source node and its local private closure. -/
set_option autoImplicit false

open Polynomial
open scoped IntermediateField

section
open AbcAdaptation AbcAdaptation.Tripod AbcAdaptation.Tripod.Fermat AbcAdaptation.Tripod.Fermat.Proper AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

open NoncriticalRegularRamificationSource

/-- Complete source local obstruction for the actual derivation and actual ramification index. -/
theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (hψP : ψ ∈ P.1) (hram : 1 < ramIdx M hDVR ψ P) :
    ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1 := by
  letI : IsCurveField M.K := M.isCurveField
  set π := P.uniformizer
  have hπ : P.ord π = 1 := P.ord_uniformizer
  have hπ0 : π ≠ 0 := P.uniformizer_ne_zero
  have hπt : Transcendental ℚ π := transcendental_of_ord_ne_zero (by omega : P.ord π ≠ 0)
  have hπO : π ∈ P.1 := P.mem_of_ord_nonneg (by omega)
  have hirr := irreducible_of_ord_eq_one P hπ
  haveI : FiniteDimensional ℚ⟮π⟯ M.K := finiteDimensional_adjoin hπt
  haveI : Algebra.IsAlgebraic ℚ⟮π⟯ M.K := isAlgebraic_adjoin hπt
  haveI : Algebra.IsAlgebraic ℚ⟮ψ⟯ M.K := isAlgebraic_adjoin hψ
  set m := minpoly ℚ (P.residue ⟨ψ, hψP⟩)
  have hsep : m.Separable := (minpoly.irreducible (P.noncritical_isIntegral_residue _)).separable
  have hm := NoncriticalElementarySource.ramIdx_of_mem M hDVR hψP
  have hmt0 : aeval ψ m ≠ 0 := fun h0 ↦ hψ ⟨m, minpoly.ne_zero (P.noncritical_isIntegral_residue _), h0⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, ramIdx M hDVR ψ P = e := ⟨(ramIdx M hDVR ψ P).toNat, by omega⟩
  have he1 : 1 ≤ e := by omega
  set u := aeval ψ m / π ^ e
  have hu0 : u ≠ 0 := div_ne_zero hmt0 (pow_ne_zero _ hπ0)
  have hu : P.1.valuation u = 1 := by
    refine valuation_eq_one_of_ord_eq_zero P hu0 ?_
    rw [P.ord_div hmt0 (pow_ne_zero _ hπ0), P.ord_pow, hπ, ← hm, he]
    ring
  have hmt : aeval ψ m = u * π ^ e := by
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hπ0)]
  obtain ⟨w, hw, hD⟩ := CurveDeriv.derivAlong_eq_unit_mul_pow_of_aeval hπt P.algebraMap_mem
    (exists_valuation_aeval_lt_one P) hπO hirr hψP hsep hu he1 hmt
  refine ⟨π, hπO, fun hDπ ↦ ?_⟩
  have h1 := CurveDeriv.derivAlong_mul_derivAlong hπt hψ
  rw [hD] at h1
  have hD0 : CurveDeriv.derivAlong ψ π ≠ 0 := by rintro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have := congrArg P.ord h1
  rw [P.ord_one, P.ord_mul hD0 (mul_ne_zero hw0 (pow_ne_zero _ hπ0)),
    P.ord_mul hw0 (pow_ne_zero _ hπ0), ord_eq_zero_of_valuation_eq_one P hw, P.ord_pow, hπ]
    at this
  have h2 := P.ord_nonneg_of_mem hDπ
  have h3 : (1 : ℤ) ≤ ((e - 1 : ℕ) : ℤ) := by omega
  omega

end

open Lean
run_meta do
  let a ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem
  let c ← getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Solution type differs"
