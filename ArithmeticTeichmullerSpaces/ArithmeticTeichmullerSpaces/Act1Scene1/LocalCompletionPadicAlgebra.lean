/-
original-path: `refer/iut/Iut/Concrete/LocalConstruct/Packet.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `4d2b6e926089b949109c69c28f13c7f878249c5d`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: selected local p-adic embedding and finite-dimensionality
proofs; independent namespace, completion alias and exact imports. No
packet, factor, tensor or archimedean construction is copied.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.Basic
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-PADIC-ALGEBRA
fidelity: constructs the continuous p-adic embedding into an actual
number-field completion and proves finite-dimensionality. This prepares
local compactness and Haar measure, not a different-untilt construction.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField IsDedekindDomain
open JoshiTeich.Prologue.Arithmetic
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [NumberField K]

abbrev completionAt (K : Type u) [Field K] [NumberField K] (w : FinitePlace K) :=
  w.maximalIdeal.adicCompletion K

section PadicEmbedding
variable (p : ℕ) [Fact p.Prime] (w : FinitePlace K)

/-- The residue characteristic detects the natural numbers in the maximal ideal. -/
lemma natCast_mem_maximalIdeal_iff (n : ℕ) :
    (n : 𝓞 K) ∈ w.maximalIdeal.asIdeal ↔ residueChar w ∣ n := by
  haveI : CharP (𝓞 K ⧸ w.maximalIdeal.asIdeal) (residueChar w) := ringChar.charP _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff _ (residueChar w)]

/-- A rational number of `p`-adic norm at most `1` has denominator prime to `p`. -/
lemma not_dvd_den_of_norm_le_one {q : ℚ} (hq : ‖(q : ℚ_[p])‖ ≤ 1) : ¬ p ∣ q.den := by
  intro hden
  have hp := (Fact.out : p.Prime)
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp [Nat.Prime.ne_one hp] at hden
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro h
    have h' : p ∣ q.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    have hg : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h' hden
    rw [Nat.Coprime.gcd_eq_one q.reduced] at hg
    exact hp.ne_one (Nat.dvd_one.mp hg)
  have hval : padicValRat p q = -(padicValNat p q.den : ℤ) := by
    unfold padicValRat
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    simp
  have h1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hden
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq0, hval, neg_neg] at hq
  have : (1 : ℚ) < (p : ℚ) ^ ((padicValNat p q.den : ℕ) : ℤ) := by
    rw [zpow_natCast]
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
  have hq' : ((p : ℚ) ^ ((padicValNat p q.den : ℕ) : ℤ)) ≤ 1 := by exact_mod_cast hq
  exact absurd (lt_of_lt_of_le this hq') (lt_irrefl _)

/-- The ring homomorphism `ℚ → K_w`, on `ℚ` with its `p`-adic uniformity. -/
noncomputable def ratHom : WithVal (Rat.padicValuation p) →+* completionAt K w :=
  (FinitePlace.embedding w.maximalIdeal).comp
    ((Rat.castHom K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)

/-- The inclusion `ℚ → ℚ_p`, on `ℚ` with its `p`-adic uniformity. -/
noncomputable abbrev padicCast : WithVal (Rat.padicValuation p) →+* ℚ_[p] :=
  (Rat.castHom ℚ_[p]).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

lemma ratHom_apply (x : WithVal (Rat.padicValuation p)) :
    ratHom p w x = ((WithVal.equiv (Rat.padicValuation p) x : ℚ) : K) := rfl

variable {p w} (hw : residueChar w = p)
include hw

omit [Fact p.Prime] in
/-- `‖p‖ < 1` in `K_w` when `w` has residue characteristic `p`. -/
lemma norm_natCast_prime_lt_one : ‖((p : K) : completionAt K w)‖ < 1 := by
  have h : ((p : K) : completionAt K w) =
      FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (p : 𝓞 K)) := by
    rw [map_natCast]; rfl
  rw [h, FinitePlace.norm_lt_one_iff_mem, natCast_mem_maximalIdeal_iff, hw]

omit [Fact p.Prime] in
/-- Rational numbers whose denominator is prime to `p` are integral in `K_w`. -/
lemma norm_ratCast_le_one (q : ℚ) (hq : ¬ p ∣ q.den) : ‖((q : K) : completionAt K w)‖ ≤ 1 := by
  have hnum : ‖((q.num : K) : completionAt K w)‖ ≤ 1 := by
    have h : ((q.num : K) : completionAt K w) =
        FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (q.num : 𝓞 K)) := by
      rw [map_intCast]; rfl
    rw [h]
    exact FinitePlace.norm_le_one K _ _
  have hden : ‖((q.den : K) : completionAt K w)‖ = 1 := by
    have h : ((q.den : K) : completionAt K w) =
        FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 K) K (q.den : 𝓞 K)) := by
      rw [map_natCast]; rfl
    rw [h, FinitePlace.norm_eq_one_iff_notMem, natCast_mem_maximalIdeal_iff, hw]
    exact hq
  have : ((q : K) : completionAt K w) =
      ((q.num : K) : completionAt K w) / ((q.den : K) : completionAt K w) := by
    rw [Rat.cast_def]
    exact map_div₀ (FinitePlace.embedding w.maximalIdeal) _ _
  rw [this, norm_div, hden, div_one]
  exact hnum

/-- `p`-adically small rationals are small in `K_w`: if `‖q‖_p ≤ p^{-m}` then
`‖q‖_w ≤ ‖p‖_w^m`. -/
lemma norm_ratCast_le (q : ℚ) (m : ℕ) (hq : ‖(q : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m) :
    ‖((q : K) : completionAt K w)‖ ≤ ‖((p : K) : completionAt K w)‖ ^ m := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set q' : ℚ := q / (p : ℚ) ^ m with hq'
  have hq'norm : ‖(q' : ℚ_[p])‖ ≤ 1 := by
    have hpm : ‖(((p : ℚ) ^ m : ℚ) : ℚ_[p])‖ = (p : ℝ)⁻¹ ^ m := by
      rw [Rat.cast_pow, Rat.cast_natCast, norm_pow, Padic.norm_p]
    rw [hq', Rat.cast_div, norm_div, hpm, div_le_one (by positivity)]
    exact hq
  have hden := not_dvd_den_of_norm_le_one p hq'norm
  have hle := norm_ratCast_le_one hw q' hden
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hqq : (q : K) = (p : K) ^ m * (q' : K) := by
    rw [hq']
    push_cast
    field_simp
  have : ((q : K) : completionAt K w) =
      FinitePlace.embedding w.maximalIdeal ((p : K) ^ m * (q' : K)) := by
    rw [hqq]; rfl
  rw [this, map_mul, map_pow, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) hle

/-- `ℚ → K_w` is uniformly continuous for the `p`-adic uniformity on `ℚ` when `w` has
residue characteristic `p`. -/
lemma uniformContinuous_ratHom : UniformContinuous (ratHom p w) := by
  have hb : (uniformity (WithVal (Rat.padicValuation p))).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {x | dist (padicCast p x.1) (padicCast p x.2) < ε}) := by
    rw [← Padic.isUniformInducing_cast_withVal.comap_uniformity]
    exact Metric.uniformity_basis_dist.comap _
  rw [hb.uniformContinuous_iff Metric.uniformity_basis_dist]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one hw)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨(p : ℝ)⁻¹ ^ m, pow_pos (inv_pos.mpr hp0) m, fun x y hxy => ?_⟩
  simp only [Set.mem_setOf_eq, dist_eq_norm, ← map_sub] at hxy ⊢
  calc ‖ratHom p w (x - y)‖
      = ‖(((WithVal.equiv (Rat.padicValuation p) (x - y) : ℚ) : K) : completionAt K w)‖ := rfl
    _ ≤ ‖((p : K) : completionAt K w)‖ ^ m := norm_ratCast_le hw _ m hxy.le
    _ < ε := hm

/-- **The embedding `ℚ_p → K_w`** at a finite place `w` of residue characteristic `p`:
the continuous extension of `ℚ → K → K_w` from the dense subring `ℚ ⊆ ℚ_p`. -/
noncomputable def padicEmb : ℚ_[p] →+* completionAt K w :=
  IsDenseInducing.extendRingHom (i := padicCast p) (f := ratHom p w)
    Padic.isUniformInducing_cast_withVal Padic.isDenseInducing_cast_withVal.dense
    (uniformContinuous_ratHom hw)

lemma padicEmb_apply (x : ℚ_[p]) :
    padicEmb hw x = (Padic.isUniformInducing_cast_withVal.isDenseInducing
      Padic.isDenseInducing_cast_withVal.dense).extend (ratHom p w) x := rfl

/-- The embedding `ℚ_p → K_w` restricts to `ℚ → K → K_w` on rational numbers. -/
lemma padicEmb_ratCast (q : ℚ) : padicEmb hw (q : ℚ_[p]) = ((q : K) : completionAt K w) := by
  have h := IsDenseInducing.extend_eq (Padic.isUniformInducing_cast_withVal.isDenseInducing
    Padic.isDenseInducing_cast_withVal.dense) (uniformContinuous_ratHom hw).continuous
    ((WithVal.equiv (Rat.padicValuation p)).symm q)
  rw [padicEmb_apply]
  have hx : padicCast p ((WithVal.equiv (Rat.padicValuation p)).symm q) = (q : ℚ_[p]) := by simp
  rw [← hx, h, ratHom_apply, RingEquiv.apply_symm_apply]

lemma continuous_padicEmb : Continuous (padicEmb hw) :=
  (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom hw)).continuous

/-- The `ℚ_p`-algebra structure of `K_w` (not an instance: it depends on `w ∣ p`). -/
noncomputable abbrev padicAlgebra : Algebra ℚ_[p] (completionAt K w) := (padicEmb hw).toAlgebra

lemma padicAlgebra_algebraMap : @algebraMap ℚ_[p] (completionAt K w) _ _ (padicAlgebra hw) =
    padicEmb hw := rfl

/-- The image of a `ℚ`-basis of `K` spans `K_w` over `ℚ_p`. -/
theorem span_range_finBasis_eq_top :
    letI := padicAlgebra hw
    Submodule.span ℚ_[p]
      (Set.range fun i => ((Module.finBasis ℚ K i : K) : completionAt K w)) = ⊤ := by
  letI := padicAlgebra hw
  haveI : ContinuousSMul ℚ_[p] (completionAt K w) :=
    continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb hw)
  let b := Module.finBasis ℚ K
  let S : Submodule ℚ_[p] (completionAt K w) :=
    Submodule.span ℚ_[p] (Set.range fun i => ((b i : K) : completionAt K w))
  haveI : FiniteDimensional ℚ_[p] S := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hS : IsClosed (S : Set (completionAt K w)) := Submodule.closed_of_finiteDimensional S
  have hrange : Set.range (algebraMap K (completionAt K w)) ⊆ S := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap K (completionAt K w) (b.repr x i • b i) =
        (b.repr x i : ℚ_[p]) • algebraMap K (completionAt K w) (b i) := by
      rw [Rat.smul_def, map_mul, Algebra.smul_def, padicAlgebra_algebraMap, padicEmb_ratCast]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [eq_top_iff]
  intro x _
  have hdense : Dense (Set.range (algebraMap K (completionAt K w))) :=
    HeightOneSpectrum.denseRange_algebraMap K w.maximalIdeal
  exact (hS.closure_subset_iff.mpr hrange) (hdense.closure_eq ▸ Set.mem_univ x)

/-- `K_w` is finite-dimensional over `ℚ_p`. -/
theorem finite_padicAlgebra :
    @Module.Finite ℚ_[p] (completionAt K w) _ _ (padicAlgebra hw).toModule := by
  letI := padicAlgebra hw
  rw [Module.finite_def, ← span_range_finBasis_eq_top hw]
  exact Submodule.fg_span (Set.finite_range _)

end PadicEmbedding
end JoshiTeich.Act1Scene1.LocalCompletion
