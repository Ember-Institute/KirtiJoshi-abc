import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorArithmeticVolume
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-DEGREE-VOLUME
source: actual tensor Haar and dimension; reference Volume.lean 18--23,
195--204 is a normalization guide, and Joshi III ss:weighted-vol is compared.
fidelity: computes log(Haar)/tensor dimension and its exponential on positive
finite scalar regions. The normalized volume is a numerical function, not
an additive Haar measure. The integral order is the actual tensor unit lattice,
not the reference maximal order or the paper theta hull.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance degreeFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance degreeFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance degreeIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem tensor_finrank_eq_localDeg_prod :
    Module.finrank ℚ_[p] P.Tensor = ∏ i, Arithmetic.localDeg (P.place i) := by
  rw [Module.finrank_eq_card_basis P.tensorBasis]
  simp only [BasisIndex, Fintype.card_pi, Fintype.card_fin, P.factor_finrank_eq_localDeg]

theorem tensor_finrank_pos : 0 < Module.finrank ℚ_[p] P.Tensor := by
  rw [P.tensor_finrank_eq_localDeg_prod]
  exact Finset.prod_pos fun i _ => Arithmetic.localDeg_pos (P.place i)

private theorem otherDimension_div_product (d : ι → ℕ) (hd : ∀ i, 0 < d i) (i : ι) :
    (FiniteTensorMatrix.otherDimension d i : ℝ) / (∏ j, d j : ℕ) = 1 / (d i : ℝ) := by
  have hprod : d i * FiniteTensorMatrix.otherDimension d i = ∏ j, d j := by
    unfold FiniteTensorMatrix.otherDimension
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [if_pos rfl, one_mul]
    have herase :
        (∏ j ∈ Finset.univ.erase i, if j = i then 1 else d j) =
          ∏ j ∈ Finset.univ.erase i, d j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.mem_erase.mp hj |>.1]
    rw [herase]
    simpa using Finset.mul_prod_erase Finset.univ d (a := i) (Finset.mem_univ i)
  have hn : (FiniteTensorMatrix.otherDimension d i : ℝ) ≠ 0 := by
    have hpos : 0 < FiniteTensorMatrix.otherDimension d i := by
      unfold FiniteTensorMatrix.otherDimension
      exact Finset.prod_pos fun j _ => by split_ifs <;> simp_all
    exact_mod_cast hpos.ne'
  have hi : (d i : ℝ) ≠ 0 := by exact_mod_cast (hd i).ne'
  rw [← hprod, Nat.cast_mul]
  field_simp [hi, hn]

/-- Real log-volume on positive finite Haar regions; `Real.log` at zero is not
the paper's extended logarithm. The public evaluation laws assume nonzero scalars. -/
def degreeLogVolume (S : Set P.Tensor) : ℝ :=
  Real.log (P.normalizedHaar S).toReal / Module.finrank ℚ_[p] P.Tensor

/-- Dimension-normalized numerical Haar volume, normalized at the tensor unit lattice. -/
def degreeVolume (S : Set P.Tensor) : ℝ :=
  (P.normalizedHaar S).toReal ^ (1 / (Module.finrank ℚ_[p] P.Tensor : ℝ))

theorem degreeVolume_eq_exp_degreeLogVolume (S : Set P.Tensor)
    (hS : 0 < (P.normalizedHaar S).toReal) :
    P.degreeVolume S = Real.exp (P.degreeLogVolume S) := by
  rw [degreeVolume, Real.rpow_def_of_pos hS, degreeLogVolume]
  congr 1
  ring

theorem degreeLogVolume_scalarLattice_eq_norm_sum
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    P.degreeLogVolume (P.scalarLattice z) =
      ∑ i, Real.log ‖z i‖ / (Arithmetic.localDeg (P.place i) : ℝ) := by
  rw [degreeLogVolume, P.normalizedHaar_scalarLattice_eq_localDeg_product z hz hz1,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _),
    P.tensor_finrank_eq_localDeg_prod,
    Real.log_prod (fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hz i))),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_pow]
  calc
    _ = Real.log ‖z i‖ *
        ((FiniteTensorMatrix.otherDimension (fun j => Arithmetic.localDeg (P.place j)) i : ℝ) /
          (∏ j, Arithmetic.localDeg (P.place j) : ℕ)) := by ring
    _ = _ := by
      rw [otherDimension_div_product _ (fun j => Arithmetic.localDeg_pos (P.place j)) i]
      ring

theorem degreeVolume_scalarLattice_eq_norm_product
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) (hz1 : ∀ i, ‖z i‖ < 1) :
    P.degreeVolume (P.scalarLattice z) =
      ∏ i, ‖z i‖ ^ (1 / (Arithmetic.localDeg (P.place i) : ℝ)) := by
  have hS : 0 < (P.normalizedHaar (P.scalarLattice z)).toReal := by
    rw [P.normalizedHaar_scalarLattice_eq_localDeg_product z hz hz1,
      ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)]
    exact Finset.prod_pos fun i _ => pow_pos (norm_pos_iff.mpr (hz i)) _
  rw [P.degreeVolume_eq_exp_degreeLogVolume _ hS,
    P.degreeLogVolume_scalarLattice_eq_norm_sum z hz hz1, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (hz i))]
  congr 1
  ring

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
