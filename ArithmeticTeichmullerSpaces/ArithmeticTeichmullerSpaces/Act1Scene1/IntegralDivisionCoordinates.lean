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
modifications: extract the monic-root and division-coordinate arguments from
inertia_fixes_of_nsmul_short'. Split the coordinate proofs and prove the
coordinate-membership result for a general model using the existing square
completion. No valuation or inertia conclusion is assumed.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutGeometricTorsionBasis
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Inertia.lean, integrality of division coordinates.
fidelity: division coordinates over an affine point with integral x coordinate
belong to the same integrally closed coefficient subalgebra, for every positive
level and every characteristic-zero Weierstrass model.
boundary: Scene1/Derived. This is the coordinate input to the inertia argument.
It does not assert that the covering is unramified or construct AG.Orbicurve.
-/

namespace JoshiTeich.Act1Scene1.IntegralDivisionCoordinates

open WeierstrassCurve Polynomial JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u v
noncomputable section

variable {K : Type v} [Field K]

/-- A root of a monic polynomial with coefficients in an integrally closed subalgebra `R` lies in
`R`. -/
lemma mem_of_monic_root_alg {k : Type*} [Field k] [Algebra k K] (R : Subalgebra k K)
    (hR : ∀ x : K, IsIntegral R x → x ∈ R) {p : K[X]} (hp : p.Monic) (hc : ∀ i, p.coeff i ∈ R)
    {x : K} (hx : p.eval x = 0) : x ∈ R := by
  have hl : p ∈ Polynomial.lifts (algebraMap R K) :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr (fun i => ⟨⟨_, hc i⟩, rfl⟩)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  exact hR x ⟨q, hqm, by rw [eval₂_eq_eval_map, hq, hx]⟩


variable {k : Type u} [Field k] [CharZero k] [Algebra k K]
  (E₀ : WeierstrassCurve k) (R : Subalgebra k K)
  (hR : ∀ x : K, IsIntegral R x → x ∈ R)

include hR in
/-- The x coordinate of a division point on a model with a₁ = a₃ = 0 is integral. -/
theorem short_division_x_mem (ha₁ : E₀.a₁ = 0) (ha₃ : E₀.a₃ = 0)
    (n : ℕ) (hn : 0 < n) {x₁ y₁ xg yg : K}
    (h₁ : (E₀⁄K).toAffine.Nonsingular x₁ y₁)
    (hG : (E₀⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ R)
    (hQ : n • Affine.Point.some x₁ y₁ h₁ = Affine.Point.some xg yg hG) : x₁ ∈ R := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have ha₁' : (E₀⁄K).toAffine.a₁ = 0 := by simp [baseChange, ha₁]
  have ha₃' : (E₀⁄K).toAffine.a₃ = 0 := by simp [baseChange, ha₃]
  have hne : ((E₀⁄K).ΨSq n).eval x₁ ≠ 0 := by
    intro h0
    have := (JoshiTeich.ReferenceIut.Torsion.smul_eq_zero_iff_ΨSq ha₁' ha₃' h₁ n).mpr h0
    rw [this] at hQ
    exact Affine.Point.some_ne_zero hG hQ.symm
  obtain ⟨X, Y, hXY, hnQ, hX⟩ := JoshiTeich.ReferenceIut.Torsion.smul_eq_of_ΨSq_ne_zero ha₁' ha₃' h₁ n hne
  have hXg : X = xg := by rw [hnQ] at hQ; exact (Affine.Point.some.inj hQ).1
  subst hXg
  let p : K[X] := (E₀⁄K).Φ n - C X * (E₀⁄K).ΨSq n
  have hΦ : (E₀⁄K).Φ n = (E₀.Φ n).map (algebraMap k K) := map_Φ _ _ _
  have hΨ : (E₀⁄K).ΨSq n = (E₀.ΨSq n).map (algebraMap k K) := map_ΨSq _ _ _
  refine mem_of_monic_root_alg R hR (p := p) ?_ ?_ ?_
  · have hmon : ((E₀⁄K).Φ n).Monic := (E₀⁄K).leadingCoeff_Φ n
    refine hmon.sub_of_left ?_
    refine degree_lt_degree ?_
    rw [(E₀⁄K).natDegree_Φ]
    refine (natDegree_C_mul_le _ _).trans_lt ?_
    have := (E₀⁄K).natDegree_ΨSq_le n
    have h1 : 1 ≤ (n : ℤ).natAbs ^ 2 := Nat.one_le_pow _ _ (by simpa using hn)
    omega
  · intro i
    simp only [p, coeff_sub, coeff_C_mul, hΦ, hΨ, coeff_map]
    exact sub_mem (R.algebraMap_mem _) (mul_mem hxg (R.algebraMap_mem _))
  · simp only [p, eval_sub, eval_mul, eval_C]
    rw [hX]; ring

include hR in
/-- The Weierstrass equation makes y integral once x belongs to the subalgebra. -/
theorem point_y_mem_of_x_mem {x y : K} (h : (E₀⁄K).toAffine.Equation x y)
    (hx : x ∈ R) : y ∈ R := by
  let a : R := ⟨algebraMap k K E₀.a₁ * x + algebraMap k K E₀.a₃,
    add_mem (mul_mem (R.algebraMap_mem _) hx) (R.algebraMap_mem _)⟩
  let b : R := ⟨x ^ 3 + algebraMap k K E₀.a₂ * x ^ 2 +
      algebraMap k K E₀.a₄ * x + algebraMap k K E₀.a₆,
    add_mem (add_mem (add_mem (pow_mem hx _) (mul_mem (R.algebraMap_mem _) (pow_mem hx _)))
      (mul_mem (R.algebraMap_mem _) hx)) (R.algebraMap_mem _)⟩
  let p : R[X] := X ^ 2 + (C a * X - C b)
  apply hR y
  refine ⟨p, ?_, ?_⟩
  · exact monic_X_pow_add ((degree_sub_le _ _).trans_lt
      (max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num))
        (degree_C_le.trans_lt (by norm_num))))
  · simp only [p, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    change y ^ 2 + ((algebraMap k K E₀.a₁ * x + algebraMap k K E₀.a₃) * y -
      (x ^ 3 + algebraMap k K E₀.a₂ * x ^ 2 + algebraMap k K E₀.a₄ * x +
        algebraMap k K E₀.a₆)) = 0
    have he := (Affine.equation_iff x y).mp h
    change y ^ 2 + algebraMap k K E₀.a₁ * x * y + algebraMap k K E₀.a₃ * y =
      x ^ 3 + algebraMap k K E₀.a₂ * x ^ 2 + algebraMap k K E₀.a₄ * x +
        algebraMap k K E₀.a₆ at he
    linear_combination he

/-- Complete the square over the coefficient field. -/
abbrev shortModel := IutGeometricTorsion.completeSquare E₀ • E₀

/-- The same change of variables over the extension field. -/
abbrev squareChange : VariableChange K :=
  (IutGeometricTorsion.completeSquare E₀).map (algebraMap k K)

omit [CharZero k] in
lemma squareChange_smul : squareChange (K := K) E₀ • (E₀⁄K) = (shortModel E₀)⁄K :=
  map_variableChange E₀ (IutGeometricTorsion.completeSquare E₀) (algebraMap k K)

/-- Point transport to the completed-square model preserves scalar multiplication. -/
def toShort : (E₀⁄K).toAffine.Point →+ ((shortModel E₀)⁄K).toAffine.Point :=
  (pointCongr (squareChange_smul E₀)).toAddMonoidHom.comp
    (vcEquiv (squareChange E₀) (E₀⁄K)).toAddMonoidHom

private lemma pointCongr_some {W W' : WeierstrassCurve K} (heq : W = W') {x y : K}
    (h : W.toAffine.Nonsingular x y) (h' : W'.toAffine.Nonsingular x y) :
    pointCongr heq (Affine.Point.some x y h) = Affine.Point.some x y h' := by
  subst W'
  rfl

omit [CharZero k] in
lemma toShort_some {x y : K} (h : (E₀⁄K).toAffine.Nonsingular x y)
    (h' : ((shortModel E₀)⁄K).toAffine.Nonsingular (vcX (squareChange E₀) x)
      (vcY (squareChange E₀) x y)) :
    toShort E₀ (Affine.Point.some x y h) = Affine.Point.some _ _ h' := by
  change pointCongr (squareChange_smul E₀)
    (vcPoint (squareChange E₀) (E₀⁄K) (Affine.Point.some x y h)) = _
  rw [vcPoint_some]
  exact pointCongr_some _ _ _

omit [CharZero k] in
lemma squareChange_x (x : K) : vcX (squareChange E₀) x = x := by
  simp [vcX, squareChange, IutGeometricTorsion.completeSquare, VariableChange.map]

include hR in
/-- Both division coordinates belong to the same integrally closed subalgebra. -/
theorem division_coordinates_mem (n : ℕ) (hn : 0 < n) {x y xg yg : K}
    (h : (E₀⁄K).toAffine.Nonsingular x y)
    (hG : (E₀⁄K).toAffine.Nonsingular xg yg) (hxg : xg ∈ R)
    (hQ : n • Affine.Point.some x y h = Affine.Point.some xg yg hG) :
    x ∈ R ∧ y ∈ R := by
  have hshort : ∀ {x y : K}, (E₀⁄K).toAffine.Nonsingular x y →
      ((shortModel E₀)⁄K).toAffine.Nonsingular (vcX (squareChange E₀) x)
        (vcY (squareChange E₀) x y) := by
    intro x y hxy
    have ht := (nonsingular_vc (squareChange E₀) (E₀⁄K) x y).mp hxy
    rwa [squareChange_smul] at ht
  have hnQ := congrArg (toShort E₀) hQ
  rw [map_nsmul, toShort_some E₀ h (hshort h), toShort_some E₀ hG (hshort hG)] at hnQ
  have hx : vcX (squareChange E₀) x ∈ R :=
    short_division_x_mem (shortModel E₀) R hR
      (IutGeometricTorsion.completeSquare_a₁ E₀)
      (IutGeometricTorsion.completeSquare_a₃ E₀) n hn (hshort h) (hshort hG)
      (by simpa only [squareChange_x] using hxg) hnQ
  rw [squareChange_x] at hx
  exact ⟨hx, point_y_mem_of_x_mem E₀ R hR h.1 hx⟩

end
end JoshiTeich.Act1Scene1.IntegralDivisionCoordinates
