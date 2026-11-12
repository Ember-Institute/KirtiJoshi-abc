/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Inertia.lean`
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source copyright and Apache-2.0 license before
copying. No NOTICE file occurs in the reference tree. Retain the notice below.
modifications: extract torsion-coordinate integrality and the inertia argument.
Use the already proved division-coordinate theorem and square-completion map.
Separate the reduction-kernel calculation and the valuation specialization.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralDivisionCoordinates
import ArithmeticTeichmullerSpaces.Act1Scene1.ReductionKernel
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Inertia.lean, inertia_fixes_of_nsmul_short' and inertia_fixes_of_nsmul.
fidelity: an automorphism in inertia that fixes an affine point fixes every
positive-level division point over it, relative to an integrally closed
subalgebra in a valuation ring, for general characteristic-zero elliptic curves.
boundary: Scene1/Derived. This proves the pointwise inertia statement. It does
not yet identify the inertia of a normalization prime or prove covering etaleness.
-/

namespace JoshiTeich.Act1Scene1.DivisionPointInertia

open WeierstrassCurve Polynomial JoshiTeich.ReferenceIut.Anabelian
open IntegralDivisionCoordinates
open scoped Classical
universe u v
noncomputable section
variable {k : Type u} [Field k] [CharZero k] {K : Type v} [Field K] [Algebra k K]

/-- The valuation is trivial on nonzero elements of its coefficient field. -/
lemma valuation_algebraMap_eq_one (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) {c : k} (hc : c ≠ 0) :
    W.valuation (algebraMap k K c) = 1 := by
  have h0 : algebraMap k K c ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap k K).injective).mpr hc
  have h1 := (W.valuation_le_one_iff _).mpr (hk c)
  have h2 := (W.valuation_le_one_iff _).mpr (hk c⁻¹)
  rw [map_inv₀, map_inv₀] at h2
  exact le_antisymm h1 ((inv_le_one₀ ((Valuation.pos_iff _).mpr h0)).mp h2)

variable (E₀ : WeierstrassCurve k) (R : Subalgebra k K)
  (hR : ∀ x : K, IsIntegral R x → x ∈ R)

include hR in
/-- The torsion points have `R`-integral `x`-coordinates. -/
lemma torsion_x_mem (ha₁ : E₀.a₁ = 0) (ha₃ : E₀.a₃ = 0) (n : ℕ) (hn : 0 < n) {x y : K} (h : (E₀⁄K).toAffine.Nonsingular x y)
    (hnt : n • (Affine.Point.some x y h : (E₀⁄K).toAffine.Point) = 0) : x ∈ R := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have ha₁' : (E₀⁄K).toAffine.a₁ = 0 := by simp [baseChange, ha₁]
  have ha₃' : (E₀⁄K).toAffine.a₃ = 0 := by simp [baseChange, ha₃]
  have hΨ := (JoshiTeich.ReferenceIut.Torsion.smul_eq_zero_iff_ΨSq ha₁' ha₃' h n).mp hnt
  have hmap : (E₀⁄K).ΨSq n = (E₀.ΨSq n).map (algebraMap k K) := map_ΨSq _ _ _
  have hn' : ((n : ℤ) : k) ≠ 0 := by exact_mod_cast hn.ne'
  let c : k := (E₀.ΨSq n).leadingCoeff
  have hc : c ≠ 0 := by
    rw [leadingCoeff_ne_zero]; intro h0
    have := E₀.leadingCoeff_ΨSq hn'
    rw [h0, leadingCoeff_zero] at this
    exact pow_ne_zero 2 hn' this.symm
  let p : K[X] := (C c⁻¹ * E₀.ΨSq n).map (algebraMap k K)
  refine mem_of_monic_root_alg R hR (p := p) ?_
    (fun i => by rw [coeff_map]; exact R.algebraMap_mem _) ?_
  · exact (monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc)).map _
  · simp only [p, Polynomial.map_mul, map_C, eval_mul, eval_C, ← hmap, hΨ, mul_zero]


include hR in
/-- Inertia fixes division points on a model with a₁ = a₃ = 0. -/
theorem inertia_fixes_short [E₀.IsElliptic] (ha₁ : E₀.a₁ = 0) (ha₃ : E₀.a₃ = 0)
    (W : ValuationSubring K) (hRW : R.toSubring ≤ W.toSubring) (σ : K →ₐ[k] K)
    (hσ : ∀ a ∈ R, W.valuation (σ a - a) < 1) (n : ℕ) (hn : 0 < n)
    {xg yg : K} (hG : (E₀⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ R)
    (hσG : Affine.Point.map (W' := E₀) (S := k) σ (Affine.Point.some xg yg hG) =
      Affine.Point.some xg yg hG)
    (Q : (E₀⁄K).toAffine.Point) (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E₀) (S := k) σ Q = Q := by
  have hk : ∀ c : k, algebraMap k K c ∈ W := fun c => hRW (R.algebraMap_mem c)
  have ha₁' : (E₀⁄K).toAffine.a₁ = 0 := by simp [baseChange, ha₁]
  have ha₃' : (E₀⁄K).toAffine.a₃ = 0 := by simp [baseChange, ha₃]
  let v := W.valuation
  have hint : ∀ z, v z ≤ 1 ↔ z ∈ W := W.valuation_le_one_iff
  have ha₂ : v (E₀⁄K).toAffine.a₂ ≤ 1 := (hint _).mpr (hk _)
  have ha₄ : v (E₀⁄K).toAffine.a₄ ≤ 1 := (hint _).mpr (hk _)
  have ha₆ : v (E₀⁄K).toAffine.a₆ ≤ 1 := (hint _).mpr (hk _)
  have h2 : v 2 = 1 := by
    have ht := valuation_algebraMap_eq_one W hk (c := (2 : k)) two_ne_zero
    rwa [map_ofNat] at ht
  have hΔ : v (E₀⁄K).toAffine.Δ = 1 := by
    have ht : (E₀⁄K).Δ = algebraMap k K E₀.Δ := by simp [baseChange]
    rw [show (E₀⁄K).toAffine.Δ = (E₀⁄K).Δ from rfl, ht]
    exact valuation_algebraMap_eq_one W hk E₀.isUnit_Δ.ne_zero
  rcases Q with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  obtain ⟨hx₁R, hy₁R⟩ := division_coordinates_mem E₀ R hR n hn h₁ hG hxg hQ
  have hx₁ : x₁ ∈ W := hRW hx₁R
  have hy₁ : y₁ ∈ W := hRW hy₁R
  have hcx : v (σ x₁ - x₁) < 1 := hσ x₁ hx₁R
  have hcy : v (σ y₁ - y₁) < 1 := hσ y₁ hy₁R
  have hmem_of_lt : ∀ z, v z < 1 → z ∈ W := fun z hz => (hint z).mp hz.le
  have hσx : σ x₁ ∈ W := by
    have ht := add_mem (hmem_of_lt _ hcx) hx₁
    simpa using ht
  have hσy : σ y₁ ∈ W := by
    have ht := add_mem (hmem_of_lt _ hcy) hy₁
    simpa using ht
  have h₁σ : (E₀⁄K).toAffine.Nonsingular (σ x₁) (σ y₁) :=
    (Affine.baseChange_nonsingular (W := E₀) (f := σ) σ.toRingHom.injective x₁ y₁).mpr h₁
  have hσQ : Affine.Point.map (W' := E₀) (S := k) σ (Affine.Point.some x₁ y₁ h₁) =
      Affine.Point.some (σ x₁) (σ y₁) h₁σ := rfl
  rw [hσQ]
  have hns := ReductionKernel.nonsingular_reduction_of_Δ v ha₁' ha₃' ha₂ ha₄ ha₆ hΔ h2 h₁σ.1
    ((hint _).mpr hσx)
  have hsub := ReductionKernel.sub_eq_zero_or_one_lt v ha₁' ha₃' ha₂ h2 h₁σ h₁
    ((hint _).mpr hσx) ((hint _).mpr hσy) ((hint _).mpr hx₁) ((hint _).mpr hy₁) hcx hcy hns
  rcases hsub with h0 | ⟨x, y, h, hxy, hv⟩
  · exact sub_eq_zero.mp h0
  · exfalso
    have htor : n • Affine.Point.some x y h = 0 := by
      rw [← hxy, smul_sub, ← hσQ, ← map_nsmul, hQ, hσG, sub_self]
    have ht := torsion_x_mem E₀ R hR ha₁ ha₃ n hn h htor
    exact absurd ((hint x).mpr (hRW ht)) (not_le.mpr hv)

omit [CharZero k] in
lemma toShort_injective : Function.Injective (toShort (K := K) E₀) :=
  (pointCongr (squareChange_smul E₀)).injective.comp
    (vcEquiv (squareChange E₀) (E₀⁄K)).injective

omit [CharZero k] in
lemma toShort_map (σ : K →ₐ[k] K) (P : (E₀⁄K).toAffine.Point) :
    toShort E₀ (Affine.Point.map (W' := E₀) (S := k) σ P) =
      Affine.Point.map (W' := shortModel E₀) (S := k) σ (toShort E₀ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · change toShort E₀ (Affine.Point.map σ 0) = Affine.Point.map σ (toShort E₀ 0)
    rw [map_zero, map_zero, map_zero]
  · have hσ : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => σ.commutes c
    have h1 := (nonsingular_vc (squareChange E₀) (E₀⁄K) x y).mp h
    rw [squareChange_smul] at h1
    rw [toShort_some E₀ h h1]
    have h2 : (E₀⁄K).toAffine.Nonsingular (σ x) (σ y) :=
      (Affine.baseChange_nonsingular (W := E₀) (f := σ) σ.toRingHom.injective x y).mpr h
    have h3 := (nonsingular_vc (squareChange E₀) (E₀⁄K) (σ x) (σ y)).mp h2
    rw [squareChange_smul] at h3
    change toShort E₀ (Affine.Point.some (σ x) (σ y) h2) = _
    rw [toShort_some E₀ h2 h3]
    refine some_ext ?_ ?_
    · simp only [vcX, squareChange, VariableChange.map, map_div₀, map_sub, map_pow,
        Units.coe_map, MonoidHom.coe_coe, hσ]
    · simp only [vcY, squareChange, VariableChange.map, map_div₀, map_sub, map_mul, map_pow,
        Units.coe_map, MonoidHom.coe_coe, hσ]

include hR in
/-- Inertia fixes every positive-level division point on a general elliptic model. -/
theorem inertia_fixes_of_nsmul [E₀.IsElliptic]
    (W : ValuationSubring K) (hRW : R.toSubring ≤ W.toSubring) (σ : K →ₐ[k] K)
    (hσ : ∀ a ∈ R, W.valuation (σ a - a) < 1) (n : ℕ) (hn : 0 < n)
    {xg yg : K} (hG : (E₀⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ R)
    (hσG : Affine.Point.map (W' := E₀) (S := k) σ (Affine.Point.some xg yg hG) =
      Affine.Point.some xg yg hG)
    (Q : (E₀⁄K).toAffine.Point) (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E₀) (S := k) σ Q = Q := by
  apply toShort_injective E₀
  rw [toShort_map]
  have hns : ((shortModel E₀)⁄K).toAffine.Nonsingular (vcX (squareChange E₀) xg)
      (vcY (squareChange E₀) xg yg) := by
    have ht := (nonsingular_vc (squareChange E₀) (E₀⁄K) xg yg).mp hG
    rwa [squareChange_smul] at ht
  have hG' := toShort_some E₀ hG hns
  refine inertia_fixes_short (shortModel E₀) R hR
    (IutGeometricTorsion.completeSquare_a₁ E₀) (IutGeometricTorsion.completeSquare_a₃ E₀)
    W hRW σ hσ n hn hns ?_ ?_ _ ?_
  · rw [squareChange_x]
    exact hxg
  · rw [← hG', ← toShort_map]
    exact congrArg (toShort E₀) hσG
  · rw [← map_nsmul, hQ]
    exact hG'

/-- A valuation subring containing k as a k-subalgebra of the ambient field. -/
def valuationSubalgebra (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) : Subalgebra k K :=
  { W.toSubring with algebraMap_mem' := hk }

omit [CharZero k] in
/-- Valuation subrings are integrally closed in the ambient field. -/
lemma valuationSubalgebra_integrallyClosed (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) (x : K)
    (hx : IsIntegral (valuationSubalgebra W hk) x) : x ∈ valuationSubalgebra W hk := by
  obtain ⟨q, hq, hqx⟩ := hx
  let f : valuationSubalgebra W hk →+* W :=
    { toFun := fun a => ⟨a.1, a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hx' : IsIntegral W x := ⟨q.map f, hq.map f, by rw [eval₂_map]; exact hqx⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx'
  rw [← hy]
  exact y.2

/-- Pointwise inertia on a valuation ring fixes division points of an integral affine point. -/
theorem inertia_fixes_of_nsmul_valuation [E₀.IsElliptic] (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) (σ : K →ₐ[k] K)
    (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1) (n : ℕ) (hn : 0 < n)
    {xg yg : K} (hG : (E₀⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ W)
    (hσG : Affine.Point.map (W' := E₀) (S := k) σ (Affine.Point.some xg yg hG) =
      Affine.Point.some xg yg hG)
    (Q : (E₀⁄K).toAffine.Point) (hQ : n • Q = Affine.Point.some xg yg hG) :
    Affine.Point.map (W' := E₀) (S := k) σ Q = Q :=
  inertia_fixes_of_nsmul E₀ (valuationSubalgebra W hk)
    (valuationSubalgebra_integrallyClosed W hk) W le_rfl σ hσ n hn hG hxg hσG Q hQ

end
end JoshiTeich.Act1Scene1.DivisionPointInertia
