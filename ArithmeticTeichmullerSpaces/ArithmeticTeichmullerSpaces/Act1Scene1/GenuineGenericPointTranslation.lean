/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionPointTranscendence

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-POINT-TRANSCENDENCE
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
the same actual elliptic function-field generic point; Mathlib point base change.
fidelity: specializes the existing algebraic-coordinate descent proof to
translation by an actual constant-field point. Subtracting that point after
descent would make the generic x-coordinate algebraic. These results are
inputs to the actual translated-generic-point function-field evaluation.
boundary: Scene1/Derived. No cusp, quotient boundary, orbicurve, or
InitialThetaGeometryProducer is supplied.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

omit [CharZero k] [E.IsElliptic] in
private lemma actualPoint_nonsingular {P : (E⁄(Ω E)).toAffine.Point} (hP : P ≠ 0) :
    (E⁄(Ω E)).toAffine.Nonsingular (ptX P) (ptY P) := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some x y h => exact h

omit [CharZero k] [E.IsElliptic] in
private lemma actualPoint_eq_some {P : (E⁄(Ω E)).toAffine.Point} (hP : P ≠ 0) :
    P = Affine.Point.some (ptX P) (ptY P) (actualPoint_nonsingular E hP) := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some x y h => rfl

/-- Translation of the generic point by a constant point is never zero. -/
theorem genericPoint_add_base_ne_zero (T : E.toAffine.Point) :
    genericPoint E + base E T ≠ 0 := by
  intro h
  apply genericPoint_ne_base E (-T)
  calc
    genericPoint E = -base E T := eq_neg_iff_add_eq_zero.mpr h
    _ = base E (-T) := (map_neg (base E) T).symm

/-- Translation preserves transcendence of the actual generic x-coordinate. -/
theorem genericPoint_add_base_x_transcendental (T : E.toAffine.Point) :
    Transcendental k (ptX (genericPoint E + base E T)) := by
  let W := (E⁄(Ω E)).toAffine
  let Q : W.Point := genericPoint E + base E T
  have hQne : Q ≠ 0 := genericPoint_add_base_ne_zero E T
  let x := ptX Q
  let y := ptY Q
  have hns : W.Nonsingular x y := actualPoint_nonsingular E hQne
  have hQeq : Q = Affine.Point.some x y hns := actualPoint_eq_some E hQne
  intro hx
  let K := algebraicClosure k (Ω E)
  let xK : K := ⟨x, mem_algebraicClosure_iff.mpr hx⟩
  let a₁K : K := algebraMap k K E.a₁
  let a₂K : K := algebraMap k K E.a₂
  let a₃K : K := algebraMap k K E.a₃
  let a₄K : K := algebraMap k K E.a₄
  let a₆K : K := algebraMap k K E.a₆
  let pK : K[X] := X ^ 2 + C (a₁K * xK + a₃K) * X -
    C (xK ^ 3 + a₂K * xK ^ 2 + a₄K * xK + a₆K)
  let f : K →ₐ[k] Ω E := IsScalarTower.toAlgHom k K (Ω E)
  have hpKcoeff : pK.coeff 2 = 1 := by
    change (X ^ 2 + C (a₁K * xK + a₃K) * X -
      C (xK ^ 3 + a₂K * xK ^ 2 + a₄K * xK + a₆K)).coeff 2 = 1
    rw [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C_of_ne_zero (by decide)]
    norm_num
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y =
      x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    simpa [W] using (W.equation_iff x y).mp hns.left
  have hmapX : f xK = x := by
    change (algebraMap K (Ω E)) xK = x
    rfl
  have hmapa₁ : f a₁K = W.a₁ := by
    change (algebraMap K (Ω E)) a₁K = W.a₁
    simp [a₁K, W]
  have hmapa₂ : f a₂K = W.a₂ := by
    change (algebraMap K (Ω E)) a₂K = W.a₂
    simp [a₂K, W]
  have hmapa₃ : f a₃K = W.a₃ := by
    change (algebraMap K (Ω E)) a₃K = W.a₃
    simp [a₃K, W]
  have hmapa₄ : f a₄K = W.a₄ := by
    change (algebraMap K (Ω E)) a₄K = W.a₄
    simp [a₄K, W]
  have hmapa₆ : f a₆K = W.a₆ := by
    change (algebraMap K (Ω E)) a₆K = W.a₆
    simp [a₆K, W]
  have hcoef1 : f (a₁K * xK + a₃K) = W.a₁ * x + W.a₃ := by
    calc
      f (a₁K * xK + a₃K) = f a₁K * f xK + f a₃K := by simp only [map_add, map_mul]
      _ = W.a₁ * x + W.a₃ := by rw [hmapa₁, hmapX, hmapa₃]
  have hcoef2 : f (xK ^ 3 + a₂K * xK ^ 2 + a₄K * xK + a₆K) =
      x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    calc
      f (xK ^ 3 + a₂K * xK ^ 2 + a₄K * xK + a₆K) =
          f xK ^ 3 + f a₂K * f xK ^ 2 + f a₄K * f xK + f a₆K := by
        simp only [map_add, map_mul, map_pow]
      _ = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
        rw [hmapX, hmapa₂, hmapa₄, hmapa₆]
  have hyK : IsAlgebraic K y := by
    refine ⟨pK, ?_, ?_⟩
    · intro hp
      have hc := congrArg (fun p : K[X] => p.coeff 2) hp
      rw [hpKcoeff, coeff_zero] at hc
      exact one_ne_zero hc
    · have hroot : (aeval y) pK = 0 := by
        change eval₂ (f : K →+* Ω E) y pK = 0
        simp only [pK, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]
        change y ^ 2 + f (a₁K * xK + a₃K) * y -
          f (xK ^ 3 + a₂K * xK ^ 2 + a₄K * xK + a₆K) = 0
        rw [hcoef1, hcoef2]
        linear_combination heq
      exact hroot
  have hy : IsAlgebraic k y := IsAlgebraic.restrictScalars k hyK
  let yK : K := ⟨y, mem_algebraicClosure_iff.mpr hy⟩
  have hnsK : ((E⁄K).toAffine).Nonsingular xK yK := by
    apply (E.toAffine.baseChange_nonsingular (f := f) f.injective xK yK).mp
    simpa [W, x, y, xK, yK, f, K] using hns
  let QK : ((E⁄K).toAffine).Point := Affine.Point.some xK yK hnsK
  have hmapQ : Affine.Point.map (W' := E.toAffine) f QK = Q := by
    change Affine.Point.map (W' := E.toAffine) f (Affine.Point.some xK yK hnsK) = Q
    rw [Affine.Point.map_some, hQeq]
    simp [f, xK, yK, x, y]
  let TK : ((E⁄K).toAffine).Point :=
    Affine.Point.baseChange (W' := E.toAffine) k K T
  have hmapT : Affine.Point.map (W' := E.toAffine) f TK = base E T := by
    exact Affine.Point.map_baseChange (W' := E.toAffine) f T
  have hmapSub : Affine.Point.map (W' := E.toAffine) f (QK - TK) = genericPoint E := by
    rw [map_sub, hmapQ, hmapT]
    exact add_sub_cancel_right (genericPoint E) (base E T)
  have hxmap (P : ((E⁄K).toAffine).Point) :
      ptX (Affine.Point.map (W' := E.toAffine) f P) = f (ptX P) := by
    cases P <;> rfl
  have hxG : xG E = f (ptX (QK - TK)) := by
    calc
      xG E = ptX (genericPoint E) := rfl
      _ = ptX (Affine.Point.map (W' := E.toAffine) f (QK - TK)) := by rw [hmapSub]
      _ = f (ptX (QK - TK)) := hxmap _
  have hGalg : IsAlgebraic k (xG E) := by
    rw [hxG]
    change IsAlgebraic k ((ptX (QK - TK) : K) : Ω E)
    exact mem_algebraicClosure_iff.mp (ptX (QK - TK)).property
  exact transcendental_xG E hGalg

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
