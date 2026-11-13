/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Independent adaptation of the concrete tripod definitions in
refer/iut/Iut/Tripod/Basic.lean. This module imports neither Iut nor Genl.
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Radical.NatInt

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped IntermediateField Classical

namespace AbcAdaptation.Tripod

abbrev Qbar : Type := AlgebraicClosure ℚ

/-- Algebraic points on the tripod, with zero and one removed. -/
def Pt : Type := {z : Qbar // z ≠ 0 ∧ z ≠ 1}

theorem isIntegral (z : Qbar) : IsIntegral ℚ z :=
  (AlgebraicClosure.isAlgebraic ℚ |>.isAlgebraic z).isIntegral

/-- Point degree as the degree of the minimal polynomial. -/
noncomputable def deg (z : Qbar) : ℕ := (minpoly ℚ z).natDegree

theorem deg_pos (z : Qbar) : 0 < deg z := minpoly.natDegree_pos (isIntegral z)

theorem deg_pos_real (z : Qbar) : (0 : ℝ) < deg z := by
  exact_mod_cast deg_pos z

noncomputable abbrev fieldOf (z : Qbar) : IntermediateField ℚ Qbar := ℚ⟮z⟯

instance (z : Qbar) : FiniteDimensional ℚ (fieldOf z) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral z)

instance (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] : NumberField F where

theorem deg_eq_finrank (z : Qbar) : deg z = Module.finrank ℚ (fieldOf z) :=
  (IntermediateField.adjoin.finrank (isIntegral z)).symm

/-- The generator of the simple intermediate field `ℚ(z)`, identified with `z`. -/
noncomputable def gen (z : Qbar) : fieldOf z := IntermediateField.AdjoinSimple.gen ℚ z

@[simp] theorem coe_gen (z : Qbar) : (gen z : Qbar) = z :=
  IntermediateField.AdjoinSimple.coe_gen ℚ z

theorem gen_ne_zero {z : Qbar} (hz : z ≠ 0) : gen z ≠ 0 := by
  intro h
  apply hz
  simpa using congrArg (fun y : fieldOf z => (y : Qbar)) h

theorem gen_sub_one_ne_zero {z : Qbar} (hz : z ≠ 1) : gen z - 1 ≠ 0 := by
  intro h
  apply hz
  have h1 : gen z = 1 := sub_eq_zero.mp h
  have := congrArg (fun y : fieldOf z => (y : Qbar)) h1
  simpa using this

def ptLE (d : ℕ) : Set Pt := {x | deg x.1 ≤ d}

def ptEQ (d : ℕ) : Set Pt := {x | deg x.1 = d}

theorem mem_ptLE {d : ℕ} {x : Pt} : x ∈ ptLE d ↔ deg x.1 ≤ d := Iff.rfl

theorem mem_ptEQ {d : ℕ} {x : Pt} : x ∈ ptEQ d ↔ deg x.1 = d := Iff.rfl

theorem ptLE_zero : ptLE 0 = ∅ := by
  ext x
  simp only [mem_ptLE, Set.mem_empty_iff_false, iff_false]
  exact Nat.not_le.mpr (deg_pos x.1)

theorem ptLE_succ (d : ℕ) : ptLE (d + 1) = ptLE d ∪ ptEQ (d + 1) := by
  ext x
  simp only [mem_ptLE, Set.mem_union, mem_ptEQ]
  exact (Nat.le_succ_iff_eq_or_le).trans or_comm

/-- Mathlib's relative number-field logarithmic height, normalized by point degree. -/
noncomputable def htCan (x : Pt) : ℝ :=
  Height.logHeight₁ (gen x.1) / deg x.1

theorem htCan_nonneg (x : Pt) : 0 ≤ htCan x :=
  div_nonneg (Height.zero_le_logHeight₁ _) (Nat.cast_nonneg _)

theorem deg_mul_htCan (x : Pt) :
    (deg x.1 : ℝ) * htCan x = Height.logHeight₁ (gen x.1) := by
  rw [htCan, mul_div_cancel₀ _ (show (deg x.1 : ℝ) ≠ 0 by
    exact_mod_cast (deg_pos x.1).ne')]

/-- Log absolute discriminant, normalized by `[ℚ(z) : ℚ]`. -/
noncomputable def logDiff (x : Pt) : ℝ :=
  Real.log |(discr (fieldOf x.1) : ℝ)| / deg x.1

theorem one_le_abs_discr_real (K : Type*) [Field K] [NumberField K] :
    (1 : ℝ) ≤ |(discr K : ℝ)| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)

theorem logDiff_nonneg (x : Pt) : 0 ≤ logDiff x :=
  div_nonneg (Real.log_nonneg (one_le_abs_discr_real _)) (Nat.cast_nonneg _)

theorem logDiff_eq_log_absNorm_differentIdeal (x : Pt) :
    logDiff x =
      Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 (fieldOf x.1)))) / deg x.1 := by
  unfold logDiff
  rw [absNorm_differentIdeal (K := fieldOf x.1), Nat.cast_natAbs, Int.cast_abs]

def badPlaces (z : Qbar) : Set (FinitePlace (fieldOf z)) :=
  {v | v (gen z) ≠ 1 ∨ v (gen z - 1) ≠ 1}

theorem mem_badPlaces {z : Qbar} {v : FinitePlace (fieldOf z)} :
    v ∈ badPlaces z ↔ v (gen z) ≠ 1 ∨ v (gen z - 1) ≠ 1 := Iff.rfl

theorem badPlaces_finite {z : Qbar} (hz : z ≠ 0 ∧ z ≠ 1) :
    (badPlaces z).Finite := by
  have h₁ := FinitePlace.hasFiniteMulSupport (gen_ne_zero hz.1)
  have h₂ := FinitePlace.hasFiniteMulSupport (gen_sub_one_ne_zero hz.2)
  refine (h₁.union h₂).subset fun v hv => ?_
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr hv

/-- Sum of residue-norm logarithms over finite places meeting `{0,1,∞}`. -/
noncomputable def logCond (x : Pt) : ℝ :=
  (∑ᶠ v : FinitePlace (fieldOf x.1),
    if v ∈ badPlaces x.1 then Real.log (Ideal.absNorm v.maximalIdeal.asIdeal) else 0) /
    deg x.1

theorem one_le_absNorm_real {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : (1 : ℝ) ≤ Ideal.absNorm v.maximalIdeal.asIdeal := by
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).le

theorem logCond_nonneg (x : Pt) : 0 ≤ logCond x := by
  classical
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply finsum_nonneg
  intro v
  split_ifs
  · exact Real.log_nonneg (one_le_absNorm_real v)
  · exact le_rfl

theorem logCond_eq_sum (x : Pt) :
    logCond x = (∑ v ∈ (badPlaces_finite x.2).toFinset,
      Real.log (Ideal.absNorm v.maximalIdeal.asIdeal)) / deg x.1 := by
  classical
  unfold logCond
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := (badPlaces_finite x.2).toFinset)]
  · rw [Finset.sum_ite_of_true]
    intro v hv
    simpa using hv
  · intro v hv
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hv
    simpa using hv.1

/-- The residue characteristic of the actual quotient of the ring of integers. -/
noncomputable def residueChar {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : ℕ :=
  ringChar (𝓞 K ⧸ v.maximalIdeal.asIdeal)

/-- A finite prime support containing `2` and a real valuation bound. -/
structure CompactlyBounded where
  V : Finset ℕ
  prime : ∀ p ∈ V, p.Prime
  two_mem : 2 ∈ V
  c : ℝ

def CompactlyBounded.set (K : CompactlyBounded) : Set Pt :=
  {x | (∀ v : FinitePlace (fieldOf x.1), residueChar v ∈ K.V →
      |Real.log (v (gen x.1))| ≤ K.c ∧ |Real.log (v (gen x.1 - 1))| ≤ K.c) ∧
    ∀ w : InfinitePlace (fieldOf x.1),
      |Real.log (w (gen x.1))| ≤ K.c ∧ |Real.log (w (gen x.1 - 1))| ≤ K.c}

theorem CompactlyBounded.mem_set {K : CompactlyBounded} {x : Pt} :
    x ∈ K.set ↔
      (∀ v : FinitePlace (fieldOf x.1), residueChar v ∈ K.V →
        |Real.log (v (gen x.1))| ≤ K.c ∧ |Real.log (v (gen x.1 - 1))| ≤ K.c) ∧
      ∀ w : InfinitePlace (fieldOf x.1),
        |Real.log (w (gen x.1))| ≤ K.c ∧ |Real.log (w (gen x.1 - 1))| ≤ K.c := Iff.rfl

/-- The rational point `q` in the algebraic closure, with zero and one excluded. -/
noncomputable def rationalPoint (q : ℚ) (h0 : q ≠ 0) (h1 : q ≠ 1) : Pt :=
  ⟨algebraMap ℚ Qbar q,
    fun h => h0 ((algebraMap ℚ Qbar).injective (h.trans (map_zero _).symm)),
    fun h => h1 ((algebraMap ℚ Qbar).injective (h.trans (map_one _).symm))⟩

/-- Statement I, fully unfolded: no compactly bounded restriction. -/
def StatementI : Prop :=
  ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ x : Pt, deg x.1 ≤ d →
    htCan x ≤ (1 + ε) * (logDiff x + logCond x) + C

/-- Statement II, fully unfolded: the same inequality on each bounded set. -/
def StatementII : Prop :=
  ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∀ K : CompactlyBounded, ∃ C : ℝ,
    ∀ x : Pt, x ∈ K.set → deg x.1 ≤ d →
      htCan x ≤ (1 + ε) * (logDiff x + logCond x) + C

def DegreeOneProjection : Prop :=
  ∀ (q : ℚ) (h0 : q ≠ 0) (h1 : q ≠ 1), deg (rationalPoint q h0 h1).1 = 1

def LogDifferentZeroProjection : Prop :=
  ∀ (q : ℚ) (h0 : q ≠ 0) (h1 : q ≠ 1), logDiff (rationalPoint q h0 h1) = 0

def HeightComparisonProjection : Prop :=
  ∀ (q : ℚ) (h0 : q ≠ 0) (h1 : q ≠ 1),
    Height.logHeight₁ q ≤ htCan (rationalPoint q h0 h1)

def RadicalConductorProjection : Prop :=
  ∀ (q : ℚ) (h0 : q ≠ 0) (h1 : q ≠ 1),
    logCond (rationalPoint q h0 h1) ≤
      Real.log
        ((UniqueFactorizationMonoid.radical
          (q.num * (q.num - (q.den : ℤ)) * (q.den : ℤ)) : ℤ) : ℝ)

end AbcAdaptation.Tripod
