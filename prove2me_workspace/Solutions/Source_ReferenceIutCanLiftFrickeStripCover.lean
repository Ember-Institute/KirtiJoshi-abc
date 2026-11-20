/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/Fuchsian/OneInftyLattice.lean
-/
import Mathlib.Tactic.FinCases
import Solutions.Source_ReferenceIutCanLiftFordCover
import Solutions.Source_ReferenceIutCanLiftFrickeNormalForm

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke

/-- The interval covering for the normal form (under the triangle inequalities). -/
private theorem normal_interval_cover {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |z * t + z| < 1 ∨ |y * t + (y - x / z)| < 1 ∨ |x * t + y / z| < 1 ∨ |z * t + 0| < 1 ∨
    |-y * t + x / z| < 1 ∨ |-x * t + (x - y / z)| < 1 ∨ |-z * t + z| < 1 := by
  obtain ⟨X, hX⟩ : ∃ X, X = x / z := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = y / z := ⟨_, rfl⟩
  rw [← hX, ← hY]
  have hXz : X * z = x := by rw [hX]; field_simp
  have hYz : Y * z = y := by rw [hY]; field_simp
  have b1 : 0 < Y - X + 1 := by
    have : (Y - X + 1) * z = y - x + z := by linear_combination hYz - hXz
    by_contra hc; push Not at hc; nlinarith
  have b2 : 0 < x + x * X - x * y + y * Y + y := by
    have : (x + x * X - x * y + y * Y + y) * z = (x + y - z) * z := by
      linear_combination x * hXz + y * hYz + hrel
    by_contra hc; push Not at hc; nlinarith
  obtain ⟨ht1, ht2⟩ := ht
  simp only [abs_lt]
  by_cases c1 : z * t + z < 1
  · left; constructor <;> nlinarith
  right
  by_cases c2 : y * t + (y - X) < 1
  · left; constructor <;> nlinarith
  right
  by_cases c3 : x * t + Y < 1
  · left; constructor <;> nlinarith
  right
  by_cases c4 : z * t + 0 < 1
  · left; constructor <;> nlinarith
  right
  by_cases c5 : -1 < -y * t + X
  · left; constructor <;> nlinarith
  right
  by_cases c6 : -1 < -x * t + (x - Y)
  · left; constructor <;> nlinarith
  right
  constructor <;> nlinarith

section NormalForm

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The commutator acts as the translation `z ↦ z + 2`. -/
private theorem commutator_n_smul (w : ℍ) : (((nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ *
    (nB hz hrel)⁻¹ : SL(2, ℝ)) • w : ℍ) : ℂ) = w + 2 := by
  rw [coe_specialLinearGroup_apply]
  have e := coe_commutator_n hz hrel
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at e00 e01 e10 e11
  simp only [Algebra.algebraMap_self, RingHom.id_apply, e00, e01, e10, e11]
  push_cast
  field_simp <;> ring

/-- **Explicit fundamental strip of the normal form group** under the triangle inequalities:
every orbit meets `-1 ≤ Re z ≤ 1`, `Im z ≥ η`. -/
theorem exists_strip_cover_normal (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y) : ∃ η > 0, ∀ w : ℍ, ∃ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel},
      γ • w ∈ {z : ℍ | z.re ∈ Icc (-1) (-1 + 2) ∧ η ≤ z.im} := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  have hA : (nA hz hrel) ∈ Γ := Subgroup.subset_closure (by simp)
  have hB : (nB hz hrel) ∈ Γ := Subgroup.subset_closure (by simp)
  set K := (nA hz hrel) * (nB hz hrel) * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹
  have hK : K ∈ Γ := mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
  let g : Fin 7 → SL(2, ℝ) :=
    ![((nA hz hrel) * (nB hz hrel))⁻¹ * K, (nB hz hrel)⁻¹, (nA hz hrel),
      (nA hz hrel) * (nB hz hrel), (nB hz hrel), (nA hz hrel)⁻¹, ((nA hz hrel) * (nB hz hrel))⁻¹]
  have hg : ∀ i, g i ∈ Γ := by
    intro i
    fin_cases i <;> simp only [g] <;>
      first
        | exact mul_mem (inv_mem (mul_mem hA hB)) hK
        | exact inv_mem hB
        | exact hA
        | exact mul_mem hA hB
        | exact hB
        | exact inv_mem hA
        | exact inv_mem (mul_mem hA hB)
  refine exists_strip_cover_of_cover (a := -1) (w := 2) (by norm_num) hK
    (commutator_n_smul hz hrel) g hg ?_
  intro t ht
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have eAB := coe_nAnB hz hrel
  have eK := coe_commutator_n hz hrel
  have e6 : ((((nA hz hrel) * (nB hz hrel))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1 / z; -z, z] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, eAB, adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have e0 : ((((nA hz hrel) * (nB hz hrel))⁻¹ * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1 / z; z, z] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, e6, eK, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rcases normal_interval_cover hx hy hz hrel h1 h2 h3 ht' with h | h | h | h | h | h | h
  · refine ⟨0, ?_⟩
    change |((((nA hz hrel * nB hz hrel)⁻¹ * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 * t +
      ((((nA hz hrel * nB hz hrel)⁻¹ * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 1| < 1
    rw [e0]; simpa using h
  · exact ⟨1, by simpa [g, coe_nB, adjugate_fin_two] using h⟩
  · exact ⟨2, by simpa [g, coe_nA] using h⟩
  · exact ⟨3, by simpa [g, eAB] using h⟩
  · exact ⟨4, by simpa [g, coe_nB] using h⟩
  · exact ⟨5, by simpa [g, coe_nA, adjugate_fin_two] using h⟩
  · refine ⟨6, ?_⟩
    change |((((nA hz hrel * nB hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 * t +
      ((((nA hz hrel * nB hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 1| < 1
    rw [e6]; simpa using h

end NormalForm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Fricke
