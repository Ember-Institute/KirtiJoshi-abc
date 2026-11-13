/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Minimal concrete types from NoncriticalP1/ElemMap.lean and actual point
evaluation facts from CurveField/Point.lean and NoncriticalBasic.lean.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
-/
import Definitions.Def_FermatCurveFieldResidue
import Definitions.Def_FermatCurveFieldZerosPoles
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

open Polynomial
open scoped Classical

namespace AbcAdaptation.Tripod.Fermat.Proper

namespace NoncriticalP1

abbrev Pt : Type := Option Tripod.Qbar

def zeroOneInf : Set Pt := {none, some 0, some 1}

theorem mem_zeroOneInf {z : Pt} : z ∈ zeroOneInf ↔
    z = none ∨ z = some 0 ∨ z = some 1 := by simp [zeroOneInf]

/-- Exact source constructors. Every map has rational coefficients and
positive degree; a Möbius matrix has nonzero determinant. -/
inductive ElemMap
  | mob (a b c d : ℚ) (h : a * d - b * c ≠ 0)
  | poly (p : ℚ[X]) (h : 0 < p.natDegree)

noncomputable def ElemMap.apply : ElemMap → Pt → Pt
  | .mob a _ c _ _, none => if c = 0 then none else some ((a / c : ℚ) : Tripod.Qbar)
  | .mob a b c d _, some z =>
    if (c : Tripod.Qbar) * z + d = 0 then none
    else some (((a : Tripod.Qbar) * z + b) / ((c : Tripod.Qbar) * z + d))
  | .poly _ _, none => none
  | .poly p _, some z => some (aeval z p)

noncomputable def ElemMap.ramIdx : ElemMap → Pt → ℕ
  | .mob .., _ => 1
  | .poly p _, none => p.natDegree
  | .poly p _, some z =>
    ((p.map (algebraMap ℚ Tripod.Qbar)) - C (aeval z p)).rootMultiplicity z

noncomputable def evalComp : List ElemMap → Pt → Pt
  | [], z => z
  | h :: hs, z => evalComp hs (h.apply z)

noncomputable def ramIdxComp : List ElemMap → Pt → ℕ
  | [], _ => 1
  | h :: hs, z => h.ramIdx z * ramIdxComp hs (h.apply z)

noncomputable def applyK {K : Type*} [Field K] [CharZero K] : ElemMap → K → K
  | .mob a b c d _, f => ((a : K) * f + b) / ((c : K) * f + d)
  | .poly p _, f => aeval f p

noncomputable def compK {K : Type*} [Field K] [CharZero K] : List ElemMap → K → K
  | [], f => f
  | h :: hs, f => compK hs (applyK h f)

end NoncriticalP1

namespace QbarPoint

variable {K : Type*} [Field K] [CharZero K] (x : QbarPoint K)

@[simp] theorem noncritical_eval_zero : x.eval 0 x.P.1.zero_mem = 0 := by
  simp [eval, show (⟨0, x.P.1.zero_mem⟩ : x.P.1) = 0 from rfl]

@[simp] theorem noncritical_eval_one : x.eval 1 x.P.1.one_mem = 1 := by
  simp [eval, show (⟨1, x.P.1.one_mem⟩ : x.P.1) = 1 from rfl]

theorem noncritical_eval_sub {f g : K} (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f - g) (sub_mem hf hg) = x.eval f hf - x.eval g hg := by
  simp only [eval, ← map_sub]
  rfl

theorem noncritical_eval_zero_iff [IsCurveField K] {f : K}
    (hf : f ∈ x.P.1) (hf0 : f ≠ 0) :
    x.eval f hf = 0 ↔ 0 < x.P.ord f := by
  rw [eval, map_eq_zero_iff _ x.σ.injective, x.P.residue_eq_zero_iff]
  exact (x.P.ord_pos_iff_mem_maximalIdeal (a := ⟨f, hf⟩) hf0).symm

theorem noncritical_exists_P_eq [IsCurveField K] (P : Place K) :
    ∃ x : QbarPoint K, x.P = P :=
  ⟨⟨P, (IsAlgClosed.lift (R := ℚ) (S := P.ResidueField)
    (M := AlgebraicClosure ℚ)).toRingHom⟩, rfl⟩

instance noncritical_finite_embeddings [IsCurveField K] (P : Place K) :
    Finite (P.ResidueField →+* Tripod.Qbar) :=
  Finite.of_equiv _ (RingHom.equivRatAlgHom P.ResidueField Tripod.Qbar).symm

/-- The full residue field and every embedding are retained. -/
theorem noncritical_finite_setOf_mem [IsCurveField K]
    {S : Set (Place K)} (hS : S.Finite) : {x : QbarPoint K | x.P ∈ S}.Finite := by
  have : Finite S := hS.to_subtype
  let g : (Σ P : S, P.1.ResidueField →+* Tripod.Qbar) → QbarPoint K :=
    fun p => ⟨p.1.1, p.2⟩
  refine (Set.finite_range g).subset fun x hx => ?_
  exact ⟨⟨⟨x.P, hx⟩, x.σ⟩, rfl⟩

end QbarPoint

variable {N : ℕ}

/-- A genuine P¹ value: infinity at a pole, actual residue embedding otherwise. -/
noncomputable def noncriticalValue (M : Model N) (x : QbarPoint M.K)
    (φ : M.K) : NoncriticalP1.Pt :=
  if h : φ ∈ x.P.1 then some (x.eval φ h) else none

noncomputable def noncriticalGalPoint (M : Model N)
    (σ : Tripod.Qbar ≃ₐ[ℚ] Tripod.Qbar) (x : QbarPoint M.K) : QbarPoint M.K :=
  ⟨x.P, σ.toAlgHom.toRingHom.comp x.σ⟩

theorem noncriticalValue_gal (M : Model N) (σ : Tripod.Qbar ≃ₐ[ℚ] Tripod.Qbar)
    (x : QbarPoint M.K) (φ : M.K) :
    noncriticalValue M (noncriticalGalPoint M σ x) φ =
      (noncriticalValue M x φ).map σ := by
  unfold noncriticalValue noncriticalGalPoint
  dsimp only
  split_ifs <;> rfl

/-- Actual zeros/poles and zeros of φ-1 have finite support for every φ.
Neither the Belyi condition nor residue finiteness is needed beyond the
curve-field facts already proved from Model. -/
theorem model_cuspsFinite (M : Model N) (hDVR : PlacesDiscrete M) (φ : M.K) :
    (cusps M hDVR φ).Finite := by
  letI : IsCurveField M.K := M.isCurveField
  have h0 := Place.finite_setOf_ord_ne_zero φ
  have h1 := Place.finite_setOf_ord_pos (φ - 1)
  refine (h0.union h1).subset fun P hP => ?_
  simpa only [cusps, Set.mem_setOf_eq, Set.mem_union, ord_eq_placeOrd] using hP

theorem noncriticalValue_zero_iff (M : Model N) (hDVR : PlacesDiscrete M)
    (x : QbarPoint M.K) {φ : M.K} (hφ0 : φ ≠ 0) :
    noncriticalValue M x φ = some 0 ↔ 0 < ord M hDVR x.P φ := by
  letI : IsCurveField M.K := M.isCurveField
  unfold noncriticalValue
  split_ifs with h
  · rw [Option.some.injEq, x.noncritical_eval_zero_iff h hφ0, ord_eq_placeOrd]
  · simp only [reduceCtorEq, false_iff, ord_eq_placeOrd, not_lt]
    exact (le_of_lt ((x.P.ord_neg_iff).mpr h))

theorem noncritical_cusp_value_iff (M : Model N) (hDVR : PlacesDiscrete M)
    (φ : M.K) (hφ : Transcendental ℚ φ) (x : QbarPoint M.K) :
    x.P ∈ cusps M hDVR φ ↔ noncriticalValue M x φ ∈ NoncriticalP1.zeroOneInf := by
  letI : IsCurveField M.K := M.isCurveField
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ
  have hφ1 : φ - 1 ≠ 0 := by
    intro h
    apply hφ
    rw [sub_eq_zero.mp h]
    exact isAlgebraic_one
  have hnone : noncriticalValue M x φ = none ↔ φ ∉ x.P.1 := by
    unfold noncriticalValue
    split_ifs with h <;> simp [h]
  have hone : noncriticalValue M x φ = some 1 ↔ 0 < x.P.ord (φ - 1) := by
    constructor
    · intro hv
      have h : φ ∈ x.P.1 := by
        by_contra hn
        simp [noncriticalValue, hn] at hv
      have hev : x.eval φ h = 1 := by simpa [noncriticalValue, h] using hv
      have h1 : φ - 1 ∈ x.P.1 := sub_mem h x.P.1.one_mem
      rw [← x.noncritical_eval_zero_iff h1 hφ1,
        x.noncritical_eval_sub h x.P.1.one_mem, hev, x.noncritical_eval_one, sub_self]
    · intro hpos
      have h1 : φ - 1 ∈ x.P.1 := x.P.mem_of_ord_nonneg hpos.le
      have h : φ ∈ x.P.1 := by simpa using add_mem h1 x.P.1.one_mem
      have hz := (x.noncritical_eval_zero_iff h1 hφ1).mpr hpos
      rw [x.noncritical_eval_sub h x.P.1.one_mem, x.noncritical_eval_one, sub_eq_zero] at hz
      simp [noncriticalValue, h, hz]
  rw [NoncriticalP1.mem_zeroOneInf, hnone, noncriticalValue_zero_iff M hDVR x hφ0,
    hone, ← x.P.ord_neg_iff]
  simp only [cusps, Set.mem_setOf_eq, ord_eq_placeOrd]
  omega

theorem noncritical_ramIdx_of_positive_order (M : Model N) (hDVR : PlacesDiscrete M)
    (φ : M.K) (P : Place M.K) (hpos : 0 < ord M hDVR P φ) :
    ramIdx M hDVR φ P = ord M hDVR P φ := by
  letI : IsCurveField M.K := M.isCurveField
  have hm : φ ∈ P.1 := P.mem_of_ord_nonneg (by simpa only [ord_eq_placeOrd] using hpos.le)
  have hn : φ ≠ 0 := by
    intro h
    simpa [h, ord_eq_placeOrd] using hpos
  have hz : P.residue ⟨φ, hm⟩ = 0 :=
    P.residue_eq_zero_iff.mpr ((P.ord_pos_iff_mem_maximalIdeal (a := ⟨φ, hm⟩) hn).mp
      (by simpa only [ord_eq_placeOrd] using hpos))
  simp [ramIdx, hm, hz, minpoly.zero, aeval_X]

end AbcAdaptation.Tripod.Fermat.Proper
