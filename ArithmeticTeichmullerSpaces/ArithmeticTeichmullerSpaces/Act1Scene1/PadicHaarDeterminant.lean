/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov

adapted-source: Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean,
Real.map_matrix_volume_pi_eq_smul_volume_pi
source-commit: 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3
modification: uses actual p-adic scalar Haar modulus and transvection laws,
with norm of the determinant in place of the real absolute value.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarScalarNorm
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarTransvection

/-!
source-id: JT-SCENE1-PADIC-HAAR-DETERMINANT
source: actual scalar norm/Haar and transvection measure preservation;
matrix diagonal/transvection generation and finite-dimensional basis transport.
fidelity: proves the determinant/norm scaling formula for arbitrary additive
Haar measures on finite-dimensional p-adic vector spaces. No measure scaling
certificate or theta-volume assumption is supplied by the caller.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PadicHaar

open MeasureTheory Matrix Set
open scoped ENNReal

noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem map_diagonal_productHaar (d : ι → ℚ_[p]) (hd : (diagonal d).det ≠ 0) :
    Measure.map (toLin' (diagonal d))
        (Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p]))) =
      ENNReal.ofReal ‖((diagonal d).det)⁻¹‖ •
        Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p])) := by
  have hm : Measurable (toLin' (diagonal d)) :=
    (toLin' (diagonal d)).continuous_of_finiteDimensional.measurable
  have hdi (i : ι) : d i ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mp (by simpa only [det_diagonal] using hd) i (Finset.mem_univ i)
  have hscale : ENNReal.ofReal ‖(diagonal d).det‖ •
      Measure.map (toLin' (diagonal d))
        (Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p]))) =
      Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p])) := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have he : (toLin' (diagonal d)) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun i => (fun x => d i * x) ⁻¹' s i) := by
      ext x
      simp only [mem_preimage, mem_univ_pi, diagonal_toLin', LinearMap.pi_apply,
        LinearMap.smul_apply, smul_eq_mul, LinearMap.coe_proj]
    rw [he, Measure.pi_pi, det_diagonal, norm_prod,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => norm_nonneg (d i)),
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [measure_preimage_mul_eq_inv_norm (Measure.addHaar : Measure ℚ_[p]) _ (hdi i),
      ← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), ← norm_mul,
      mul_inv_cancel₀ (hdi i), norm_one, ENNReal.ofReal_one, one_mul]
  conv_rhs => rw [← hscale]
  rw [smul_smul, ← ENNReal.ofReal_mul (norm_nonneg _), ← norm_mul,
    inv_mul_cancel₀ hd, norm_one, ENNReal.ofReal_one, one_smul]

theorem map_matrix_productHaar_eq_norm_det_inv
    (M : Matrix ι ι ℚ_[p]) (hM : M.det ≠ 0) :
    Measure.map (toLin' M) (Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p]))) =
      ENNReal.ofReal ‖M.det⁻¹‖ •
        Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p])) := by
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · exact map_diagonal_productHaar
  · intro t
    rw [t.det, inv_one, norm_one, ENNReal.ofReal_one, one_smul]
    exact (productHaar_measurePreserving_transvection t).map_eq
  · intro A B hA hB hIA hIB
    rw [toLin'_mul, det_mul, LinearMap.coe_comp,
      ← Measure.map_map (toLin' A).continuous_of_finiteDimensional.measurable
        (toLin' B).continuous_of_finiteDimensional.measurable,
      hIB, Measure.map_smul,
      hIA, smul_smul, mul_inv, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    rw [mul_comm]

theorem map_matrix_haar_eq_norm_det_inv (μ : Measure (ι → ℚ_[p])) [μ.IsAddHaarMeasure]
    (M : Matrix ι ι ℚ_[p]) (hM : M.det ≠ 0) :
    Measure.map (toLin' M) μ = ENNReal.ofReal ‖M.det⁻¹‖ • μ := by
  let ν := Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p]))
  have hm := (toLin' M).continuous_of_finiteDimensional.measurable
  have hμ : μ = Measure.addHaarScalarFactor μ ν • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  rw [hμ, Measure.map_smul,
    map_matrix_productHaar_eq_norm_det_inv M hM, smul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E] [MeasurableSpace E] [BorelSpace E]

theorem map_linearEquiv_haar_eq_norm_det_inv (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E ≃L[ℚ_[p]] E) :
    Measure.map f μ = ENNReal.ofReal ‖(LinearMap.det f.toLinearEquiv.toLinearMap)⁻¹‖ • μ := by
  let e := (Module.finBasis ℚ_[p] E).equivFunL
  let g := (e.symm.trans f).trans e
  let M := LinearMap.toMatrix' g.toLinearEquiv.toLinearMap
  have hdet : M.det = LinearMap.det f.toLinearEquiv.toLinearMap := by
    rw [LinearMap.det_toMatrix']
    exact LinearMap.det_conj f.toLinearEquiv.toLinearMap e.toLinearEquiv
  have hM : M.det ≠ 0 := by
    rw [hdet]
    exact f.toLinearEquiv.isUnit_det'.ne_zero
  let ν := μ.map e
  haveI : ν.IsAddHaarMeasure :=
    e.toLinearEquiv.toAddEquiv.isAddHaarMeasure_map μ e.continuous e.symm.continuous
  have hg := map_matrix_haar_eq_norm_det_inv ν M hM
  rw [Matrix.toLin'_toMatrix', hdet] at hg
  change Measure.map g ν =
    ENNReal.ofReal ‖(LinearMap.det f.toLinearEquiv.toLinearMap)⁻¹‖ • ν at hg
  have hconj : (f : E → E) = e.symm ∘ (g ∘ e) := by
    funext x
    simp only [Function.comp_apply, g, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [hconj, ← Measure.map_map e.symm.continuous.measurable (g.continuous.comp e.continuous).measurable,
    ← Measure.map_map g.continuous.measurable e.continuous.measurable]
  change Measure.map e.symm (Measure.map g ν) = _
  rw [hg, Measure.map_smul,
    Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  have hid : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  rw [hid, Measure.map_id]

theorem measure_image_linearEquiv_eq_norm_det (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E ≃L[ℚ_[p]] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal ‖LinearMap.det f.toLinearEquiv.toLinearMap‖ * μ s := by
  have h := map_linearEquiv_haar_eq_norm_det_inv μ f.symm
  have hs := congrArg (fun ν : Measure E => ν s) h
  change (Measure.map f.symm.toHomeomorph.toMeasurableEquiv μ) s = _ at hs
  rw [f.symm.toHomeomorph.toMeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul] at hs
  change μ (f.symm ⁻¹' s) =
    ENNReal.ofReal ‖(LinearMap.det f.symm.toLinearEquiv.toLinearMap)⁻¹‖ * μ s at hs
  have he : f.symm ⁻¹' s = f '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm x, hx, f.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [he] at hs
  have hd : LinearMap.det f.symm.toLinearEquiv.toLinearMap =
      (LinearMap.det f.toLinearEquiv.toLinearMap)⁻¹ := by
    exact LinearEquiv.det_coe_symm f.toLinearEquiv
  rw [hd, inv_inv] at hs
  exact hs

end
end JoshiTeich.Act1Scene1.PadicHaar
