import Definitions.Def_FermatCurveDerivationAdjoin
import Mathlib.RingTheory.Unramified.Field
import Definitions.Def_FermatNoncriticalElementarySource
import Definitions.Def_FermatCurveFieldUniformizer
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_eq_unit_mul_pow_of_aeval
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_CurveDeriv_derivAlong_unit_mul_pow
import Definitions.Def_FermatProperDivisorHeight

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source proof from Belyi/CurveDeriv/Basic.lean:68-95,178-219,
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The proof closure already exists privately in the current regular-ramification
source theorem. Only the chain and reciprocal results become public here.
See this unit's validation receipts and source mappings.
-/

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

theorem derivAlong_eq_smul (s : K) (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong s = derivAlong s t • derivAlong t :=
  eq_smul_derivAlong ht _

theorem derivAlong_mul_derivAlong {s : K} (hs : Transcendental ℚ s) [Algebra.IsAlgebraic ℚ⟮s⟯ K]
    (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t s * derivAlong s t = 1 := by
  have := congrArg (· s) (derivAlong_eq_smul s ht)
  simp only [derivAlong_self hs, Derivation.smul_apply, smul_eq_mul] at this
  rw [this, mul_comm]


end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source proof from pinned Belyi RamIdx.lean:237-284,
CurveDeriv/Order.lean:83-100, and their local uniformizer/unit closure.
Pin: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The proved regular local theorem and unit-times-power theorem are imported.
The current integer index and actual places remain unchanged.
See this unit's validation receipts and source mappings.
-/

open scoped Classical

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

/- Source Order.lean:83-100. The regular counterpart is already public. -/
namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}
  (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr

/-- Source pole computation, with the same positive pole order and unit. -/
theorem derivAlong_eq_unit_mul_zpow_of_inv {t : K} {u : K} (hu : O.valuation u = 1) {e : ℕ}
    (he : 1 ≤ e) (htu : t⁻¹ = u * π ^ e) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π t = w * π ^ (-(e + 1 : ℤ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hπ0 : π ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  obtain ⟨w₀, hw₀, hD⟩ := derivAlong_unit_mul_pow ht hQ hres hπO hirr hu k
  refine ⟨-(u⁻¹ ^ 2 * w₀), by rw [Valuation.map_neg, map_mul, map_pow, map_inv₀, hu, hw₀]; simp,
    ?_⟩
  have ht' : t = (u * π ^ (k + 1))⁻¹ := by rw [← htu, inv_inv]
  rw [ht', Derivation.leibniz_inv, hD, smul_eq_mul]
  rw [show (-(((k + 1 : ℕ) : ℤ) + 1)) = -(k : ℤ) - 2 by push_cast; ring, zpow_sub₀ hπ0,
    zpow_neg, zpow_natCast]
  field_simp
  ring

end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

namespace AbcAdaptation.Tripod.Fermat.Proper.DifferentialOrderSource

open NoncriticalRegularRamificationSource

/-- Source RamIdx.lean:237. The exact current integer index is used. -/
theorem ord_derivAlong_of_mem {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) (P : Place M.K) (hψP : ψ ∈ P.1) :
    letI : IsCurveField M.K := M.isCurveField
    P.ord (CurveDeriv.derivAlong P.uniformizer ψ) = ramIdx M hDVR ψ P - 1 := by
  letI : IsCurveField M.K := M.isCurveField
  set π := P.uniformizer
  have hπ : P.ord π = 1 := P.ord_uniformizer
  have hπ0 : π ≠ 0 := P.uniformizer_ne_zero
  have hπt : Transcendental ℚ π := transcendental_of_ord_ne_zero (by omega : P.ord π ≠ 0)
  have hπO : π ∈ P.1 := P.mem_of_ord_nonneg (by omega)
  have hirr := irreducible_of_ord_eq_one P hπ
  haveI : FiniteDimensional ℚ⟮π⟯ M.K := finiteDimensional_adjoin hπt
  set m := minpoly ℚ (P.residue ⟨ψ, hψP⟩)
  have hsep : m.Separable := (minpoly.irreducible (P.noncritical_isIntegral_residue _)).separable
  have hm := NoncriticalElementarySource.ramIdx_of_mem M hDVR hψP
  have hmt0 : aeval ψ m ≠ 0 := fun h0 ↦ hψ ⟨m, minpoly.ne_zero (P.noncritical_isIntegral_residue _), h0⟩
  have hpos := noncriticalRamificationPositive M hDVR ψ hψ P
  obtain ⟨e, he⟩ : ∃ e : ℕ, ramIdx M hDVR ψ P = e :=
    ⟨(ramIdx M hDVR ψ P).toNat, by omega⟩
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
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  change P.ord (CurveDeriv.derivAlong π ψ) = ramIdx M hDVR ψ P - 1
  rw [hD, P.ord_mul hw0 (pow_ne_zero _ hπ0), P.ord_pow, hπ,
    ord_eq_zero_of_valuation_eq_one P hw]
  omega

/-- Source RamIdx.lean:257. The equality includes every actual pole. -/
theorem ord_derivAlong_of_notMem {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (ψ : M.K) (P : Place M.K) (hψP : ψ ∉ P.1) :
    letI : IsCurveField M.K := M.isCurveField
    P.ord (CurveDeriv.derivAlong P.uniformizer ψ) = -ramIdx M hDVR ψ P - 1 := by
  letI : IsCurveField M.K := M.isCurveField
  set π := P.uniformizer
  have hπ : P.ord π = 1 := P.ord_uniformizer
  have hπ0 : π ≠ 0 := P.uniformizer_ne_zero
  have hπt : Transcendental ℚ π := transcendental_of_ord_ne_zero (by omega : P.ord π ≠ 0)
  have hπO : π ∈ P.1 := P.mem_of_ord_nonneg (by omega)
  have hirr := irreducible_of_ord_eq_one P hπ
  haveI : FiniteDimensional ℚ⟮π⟯ M.K := finiteDimensional_adjoin hπt
  have hψ0 : ψ ≠ 0 := fun h0 ↦ hψP (h0 ▸ P.1.zero_mem)
  have hneg := (P.ord_neg_iff).mpr hψP
  have hm := NoncriticalElementarySource.ramIdx_of_notMem M hDVR hψP
  obtain ⟨e, he⟩ : ∃ e : ℕ, ramIdx M hDVR ψ P = e :=
    ⟨(ramIdx M hDVR ψ P).toNat, by omega⟩
  have he1 : 1 ≤ e := by omega
  set u := ψ⁻¹ / π ^ e
  have hu0 : u ≠ 0 := div_ne_zero (inv_ne_zero hψ0) (pow_ne_zero _ hπ0)
  have hu : P.1.valuation u = 1 := by
    refine valuation_eq_one_of_ord_eq_zero P hu0 ?_
    rw [P.ord_div (inv_ne_zero hψ0) (pow_ne_zero _ hπ0), P.ord_inv, P.ord_pow, hπ]
    omega
  have htu : ψ⁻¹ = u * π ^ e := by
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hπ0)]
  obtain ⟨w, hw, hD⟩ := CurveDeriv.derivAlong_eq_unit_mul_zpow_of_inv hπt P.algebraMap_mem
    (exists_valuation_aeval_lt_one P) hπO hirr hu he1 htu
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  change P.ord (CurveDeriv.derivAlong π ψ) = -ramIdx M hDVR ψ P - 1
  rw [hD, P.ord_mul hw0 (zpow_ne_zero _ hπ0), P.ord_zpow, hπ,
    ord_eq_zero_of_valuation_eq_one P hw]
  omega

/-- The source coefficient formula at all proper places. -/
theorem ord_derivAlong {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) (P : Place M.K) :
    letI : IsCurveField M.K := M.isCurveField
    P.ord (CurveDeriv.derivAlong P.uniformizer ψ) =
      if ψ ∈ P.1 then ramIdx M hDVR ψ P - 1 else -ramIdx M hDVR ψ P - 1 := by
  letI : IsCurveField M.K := M.isCurveField
  by_cases h : ψ ∈ P.1
  · rw [if_pos h]
    exact ord_derivAlong_of_mem M hDVR ψ hψ P h
  · rw [if_neg h]
    exact ord_derivAlong_of_notMem M hDVR ψ P h

/-- Source RamIdx.lean:278: nonzero differential factor before product order. -/
theorem derivAlong_uniformizer_ne_zero {N : ℕ} (M : Model N)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) (P : Place M.K) :
    letI : IsCurveField M.K := M.isCurveField
    CurveDeriv.derivAlong P.uniformizer ψ ≠ 0 := by
  letI : IsCurveField M.K := M.isCurveField
  have hπt : Transcendental ℚ P.uniformizer :=
    transcendental_of_ord_ne_zero (by rw [P.ord_uniformizer]; exact one_ne_zero)
  haveI : Algebra.IsAlgebraic ℚ⟮P.uniformizer⟯ M.K := isAlgebraic_adjoin hπt
  haveI : Algebra.IsAlgebraic ℚ⟮ψ⟯ M.K := isAlgebraic_adjoin hψ
  intro h0
  have h1 := CurveDeriv.derivAlong_mul_derivAlong hπt hψ
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

end AbcAdaptation.Tripod.Fermat.Proper.DifferentialOrderSource

/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent source proof from Belyi/CurveField/Canonical.lean:144-166,
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The supplied actual canonical divisor and every proper place remain quantified.
See this unit's validation receipts and source mappings.
-/

set_option autoImplicit false
open scoped Classical IntermediateField

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- The source chain rule, with q = du/dφ and positive principal order. -/
theorem canonicalDifferentialChange_source {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : Transcendental ℚ φ) (K : CanonicalDivisorData M hDVR) :
    ∃ q : M.K, q ≠ 0 ∧ ∀ P : Place M.K,
      K.D P =
        (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
          else -ramIdx M hDVR φ P - 1) + ord M hDVR P q := by
  letI : IsCurveField M.K := M.isCurveField
  haveI : Algebra.IsAlgebraic ℚ⟮M.u⟯ M.K := isAlgebraic_adjoin M.transcendental_u
  haveI : Algebra.IsAlgebraic ℚ⟮φ⟯ M.K := isAlgebraic_adjoin hφ
  let q : M.K := CurveDeriv.derivAlong φ M.u
  have hq : q ≠ 0 := by
    intro h0
    have h1 := CurveDeriv.derivAlong_mul_derivAlong M.transcendental_u hφ
    rw [show CurveDeriv.derivAlong φ M.u = 0 from h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨q, hq, ?_⟩
  intro P
  rw [K.coefficient P]
  have hu := DifferentialOrderSource.ord_derivAlong M hDVR M.u M.transcendental_u P
  have hφorder := DifferentialOrderSource.ord_derivAlong M hDVR φ hφ P
  have hchain := congrArg (· M.u) (CurveDeriv.derivAlong_eq_smul P.uniformizer hφ)
  simp only [Derivation.smul_apply, smul_eq_mul] at hchain
  calc
    (if M.u ∈ P.1 then ramIdx M hDVR M.u P - 1 else -ramIdx M hDVR M.u P - 1) =
        P.ord (CurveDeriv.derivAlong P.uniformizer M.u) := hu.symm
    _ = P.ord (CurveDeriv.derivAlong P.uniformizer φ) + P.ord q := by
      rw [hchain, P.ord_mul
        (DifferentialOrderSource.derivAlong_uniformizer_ne_zero M φ hφ P) hq]
    _ = (if φ ∈ P.1 then ramIdx M hDVR φ P - 1 else -ramIdx M hDVR φ P - 1) +
          ord M hDVR P q := by rw [hφorder, ord_eq_placeOrd]

end AbcAdaptation.Tripod.Fermat.Proper

open AbcAdaptation.Tripod.Fermat.Proper

theorem solution {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (φ : M.K) (hφ : Transcendental ℚ φ) (K : CanonicalDivisorData M hDVR) :
    ∃ q : M.K, q ≠ 0 ∧ ∀ P : Place M.K,
      K.D P =
        (if φ ∈ P.1 then ramIdx M hDVR φ P - 1
          else -ramIdx M hDVR φ P - 1) + ord M hDVR P q := by
  exact AbcAdaptation.Tripod.Fermat.Proper.canonicalDifferentialChange_source M hDVR hRF φ hφ K
