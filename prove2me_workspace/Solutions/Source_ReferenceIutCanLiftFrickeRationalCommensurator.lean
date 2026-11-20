/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Rational.lean
-/
import Solutions.Source_ReferenceIutCanLiftFrickeRational
import Solutions.Source_ReferenceIutCanLiftFrickeTraceField

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (nA nB)

private noncomputable abbrev ratSubfield : Subfield ℝ := (Rat.castHom ℝ).fieldRange

private theorem mem_rat_iff {r : ℝ} : r ∈ ratSubfield ↔ ∃ q : ℚ, (q : ℝ) = r :=
  RingHom.mem_fieldRange

/-- A real multiple of a rational matrix with nonzero rational trace has rational entries. -/
lemma slIn_of_isRatMul {g : SL(2, ℝ)} (hg : IsRatMul g) (htr : trace (g : Matrix (Fin 2) (Fin 2) ℝ)
    ∈ ratSubfield) (htr0 : trace (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) : SLIn ratSubfield g := by
  obtain ⟨c, hc, R, hR⟩ := hg
  have htrR : trace (g : Matrix (Fin 2) (Fin 2) ℝ) = c * ((trace R : ℚ) : ℝ) := by
    rw [hR, trace_smul, smul_eq_mul, ← AddMonoidHom.map_trace (Rat.castHom ℝ) R]
    rfl
  have hR0 : ((trace R : ℚ) : ℝ) ≠ 0 := by
    intro hzero
    exact htr0 (by rw [htrR, hzero, mul_zero])
  have hcQ : c ∈ ratSubfield := by
    have : c = trace (g : Matrix (Fin 2) (Fin 2) ℝ) / ((trace R : ℚ) : ℝ) := by
      rw [htrR, mul_div_cancel_right₀ _ hR0]
    rw [this]
    exact div_mem htr (mem_rat_iff.2 ⟨_, rfl⟩)
  intro i j
  rw [hR, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  exact mul_mem hcQ (mem_rat_iff.2 ⟨_, rfl⟩)

/-- From `(g⁻¹)ᵢₚ g_qj ∈ ℚ` for all indices, `g` is a real multiple of a rational matrix. -/
lemma isRatMul_of_mul_mem {g : SL(2, ℝ)}
    (h : ∀ i p q j, ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p *
      (g : Matrix (Fin 2) (Fin 2) ℝ) q j ∈ ratSubfield) : IsRatMul g := by
  classical
  have hne : ∃ i p, ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p ≠ 0 := by
    by_contra hno
    push Not at hno
    have : ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by ext i p; exact hno i p
    have hdet := (g⁻¹).det_coe
    rw [this, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨i, p, hip⟩ := hne
  choose R hR using fun q j ↦ mem_rat_iff.1 (h i p q j)
  refine ⟨(((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p)⁻¹, inv_ne_zero hip,
    Matrix.of fun q j ↦ R q j, ?_⟩
  ext q j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, Rat.coe_castHom,
    hR, inv_mul_cancel_left₀ hip]

section normalForm

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
  {X Y Z : ℚ} (hX : x ^ 2 = (X : ℝ)) (hY : y ^ 2 = (Y : ℝ)) (hZ : z ^ 2 = (Z : ℝ))

private theorem fricke_product_eq_rat (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hX : x ^ 2 = (X : ℝ)) (hY : y ^ 2 = (Y : ℝ)) (hZ : z ^ 2 = (Z : ℝ)) :
    x * y * z = ((X + Y + Z : ℚ) : ℝ) := by
  push_cast
  rw [← hX, ← hY, ← hZ, hrel]

include hX hY hZ in
/-- **C7 over `ℚ`.** Every element of the commensurator is a real multiple of a rational matrix. -/
theorem isRatMul_of_mem_commensurator {δ : SL(2, ℝ)}
    (hδ : δ ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) : IsRatMul δ := by
  set W : ℚ := X + Y + Z
  have hW : x * y * z = W := fricke_product_eq_rat hrel hX hY hZ
  have hax : x * (x - y / z) ∈ ratSubfield := by
    refine mem_rat_iff.2 ⟨X - W / Z, ?_⟩
    push_cast
    rw [← hX, ← hZ, ← hW]
    field_simp [hz.ne'] <;> ring
  have hbx : (x - y / z) ^ 2 ∈ ratSubfield := by
    refine mem_rat_iff.2 ⟨X - 2 * W / Z + Y / Z, ?_⟩
    push_cast
    rw [← hX, ← hY, ← hZ, ← hW]
    field_simp [hz.ne'] <;> ring
  have hcx : x ^ 2 ∈ ratSubfield := mem_rat_iff.2 ⟨X, hX.symm⟩
  refine isRatMul_of_mul_mem (mul_mem_of_mem_commensurator' ratSubfield hz hrel hax hbx hcx ?_ hδ)
  intro n γ hγ htr
  refine slIn_of_isRatMul (isRatMul_of_mem_normalForm hz hrel hX hY hZ hγ) ?_ ?_ <;> rw [htr]
  · exact mem_rat_iff.2 ⟨2 * (-1) ^ n, by push_cast; rfl⟩
  · exact mul_ne_zero two_ne_zero (pow_ne_zero _ (by norm_num))

end normalForm

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
