/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov

adapted-source: Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean,
Real.volume_preserving_transvectionStruct
source-commit: 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3
modification: replaces real Lebesgue measure by p-adic product Haar measure;
transports the result to arbitrary Haar measures and finite-dimensional bases.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarScaling
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Group.LIntegral

/-!
source-id: JT-SCENE1-PADIC-HAAR-TRANSVECTION
source: Mathlib finite-product Fubini and translation invariance, and matrix
transvections; the real transvection proof supplies the proof structure.
fidelity: proves p-adic elementary shears preserve actual additive Haar
measure, then transports this law through any finite-dimensional basis.
This is the transvection step of determinant/Haar accounting; diagonal
scaling and the complete determinant formula are still separate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PadicHaar

open MeasureTheory Matrix Set
open scoped ENNReal

noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem productHaar_measurePreserving_transvection
    (t : TransvectionStruct ι ℚ_[p]) :
    MeasurePreserving (toLin' t.toMatrix)
      (Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p])))
      (Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p]))) := by
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ => hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self (μ := (Measure.addHaar : Measure ℚ_[p]))
      (fun xᵢ => indicator (univ.pi s) 1 (Function.update x t_i xᵢ))]

theorem haar_measurePreserving_transvection
    (μ : Measure (ι → ℚ_[p])) [μ.IsAddHaarMeasure]
    (t : TransvectionStruct ι ℚ_[p]) :
    MeasurePreserving (toLin' t.toMatrix) μ μ := by
  let ν := Measure.pi (fun _ : ι => (Measure.addHaar : Measure ℚ_[p]))
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  have hμ : μ = Measure.addHaarScalarFactor μ ν • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  rw [hμ, Measure.map_smul _ ht.aemeasurable, (productHaar_measurePreserving_transvection t).map_eq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E] [MeasurableSpace E] [BorelSpace E]

def basisTransvection (b : Module.Basis ι ℚ_[p] E) (t : TransvectionStruct ι ℚ_[p]) :
    E ≃L[ℚ_[p]] E :=
  (b.equivFunL.trans
    (Matrix.toLin'OfInv t.inv_mul t.mul_inv).toContinuousLinearEquiv).trans b.equivFunL.symm

theorem haar_measurePreserving_basisTransvection
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (b : Module.Basis ι ℚ_[p] E) (t : TransvectionStruct ι ℚ_[p]) :
    MeasurePreserving (basisTransvection b t) μ μ := by
  let e := b.equivFunL
  let ν := μ.map e
  haveI : ν.IsAddHaarMeasure :=
    e.toLinearEquiv.toAddEquiv.isAddHaarMeasure_map μ e.continuous e.symm.continuous
  have h := (haar_measurePreserving_transvection ν t).map_eq
  refine ⟨(basisTransvection b t).continuous.measurable, ?_⟩
  change Measure.map (e.symm ∘ (toLin' t.toMatrix ∘ e)) μ = μ
  rw [← Measure.map_map e.symm.continuous.measurable
    (((toLin' t.toMatrix).continuous_of_finiteDimensional).comp e.continuous).measurable,
    ← Measure.map_map (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
      e.continuous.measurable]
  change Measure.map e.symm (Measure.map (toLin' t.toMatrix) ν) = μ
  rw [h, Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  have hcomp : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  rw [hcomp, Measure.map_id]

end
end JoshiTeich.Act1Scene1.PadicHaar
