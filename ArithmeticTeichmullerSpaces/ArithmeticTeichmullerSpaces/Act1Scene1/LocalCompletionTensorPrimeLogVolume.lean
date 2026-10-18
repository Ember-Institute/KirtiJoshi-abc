/-
original-path: `refer/iut/Iut/Concrete/LocalConstruct/Volume.lean` (277--300)
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `b76207ab8955e68a7408d5d2a770b75a30c3bebf`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project LICENSE)
modification: actual completion Packet, normalizationHaar already normalized
at the integral closure, and positive finite preimage measure laws.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationLogVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicHaarScaling

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-PRIME-LOG-VOLUME
source: reference Volume.componentVol_prime_preimage', Cor312/LogVolume's
positive finite principal-region scaling law; IUT III Proposition 3.9(i).
fidelity: actual normalization Haar and degree-normalized real logarithm.
Measurability and positive finite measure are explicit; no law on null sets.
boundary: Scene1/Derived; no paper theta or volume identification.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance primeFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance primeFactorFinite (i : ι) : FiniteDimensional ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)

/-- The inverse image under multiplication by the residue prime. -/
def primePreimage (U : Set P.Tensor) : Set P.Tensor :=
  (fun x => (p : P.Tensor) * x) ⁻¹' U

omit [Fintype ι] in
theorem natCast_mul_eq_smul (x : P.Tensor) :
    (p : P.Tensor) * x = (p : ℚ_[p]) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem normalizationHaar_primePreimage {U : Set P.Tensor} (hU : MeasurableSet U) :
    P.normalizationHaar (P.primePreimage U) =
      (p : ENNReal) ^ Module.finrank ℚ_[p] P.Tensor * P.normalizationHaar U := by
  have he : P.primePreimage U = (fun x => (p : ℚ_[p]) • x) ⁻¹' U := by
    ext x
    simp only [primePreimage, Set.mem_preimage, P.natCast_mul_eq_smul]
  rw [he]
  exact PadicHaar.measure_preimage_smul_padic P.normalizationHaar hU

theorem primePreimage_measurableSet {U : Set P.Tensor} (hU : MeasurableSet U) :
    MeasurableSet (P.primePreimage U) := by
  have he : P.primePreimage U = (fun x => (p : ℚ_[p]) • x) ⁻¹' U := by
    ext x
    simp only [primePreimage, Set.mem_preimage, P.natCast_mul_eq_smul]
  rw [he]
  exact hU.preimage (continuous_id.const_smul (p : ℚ_[p])).measurable

theorem primePreimage_haar_pos_lt_top {U : Set P.Tensor} (hU : MeasurableSet U)
    (hpos : 0 < P.normalizationHaar U) (hfin : P.normalizationHaar U < ⊤) :
    0 < P.normalizationHaar (P.primePreimage U) ∧
      P.normalizationHaar (P.primePreimage U) < ⊤ := by
  rw [P.normalizationHaar_primePreimage hU]
  have hp : (p : ENNReal) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact ⟨pos_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp) hpos.ne'),
    ENNReal.mul_lt_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)).lt_top hfin⟩

/-- Degree normalization cancels the dimension in the Haar modulus. -/
theorem normalizationLogVolume_primePreimage {U : Set P.Tensor} (hU : MeasurableSet U)
    (hpos : 0 < P.normalizationHaar U) (hfin : P.normalizationHaar U < ⊤) :
    P.normalizationLogVolume (P.primePreimage U) =
      P.normalizationLogVolume U + Real.log p := by
  have hn : (Module.finrank ℚ_[p] P.Tensor : ℝ) ≠ 0 := by
    exact_mod_cast P.tensor_finrank_pos.ne'
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hm : (P.normalizationHaar U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  unfold normalizationLogVolume
  rw [P.normalizationHaar_primePreimage hU, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, Real.log_mul (pow_ne_zero _ hp.ne') hm, Real.log_pow,
    add_div, mul_div_cancel_left₀ _ hn, add_comm]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
