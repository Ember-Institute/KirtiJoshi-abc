import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraNormGeneral
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorDegreeVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorWeightDescent

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-WEIGHTED-REGION-VOLUME
source: actual tensor determinant/Haar law, general completion norm identity,
and Joshi III ss:weighted-vol (3522--3557).
fidelity: computes actual Haar and degree volume for every nonzero scalar
presentation. Constructs a region function realizing arbitrary real factor
weights exactly when weight times local degree is constant. This is a numerical
power of Haar, not an additive measure. No paper theta or untilt identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance weightedFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance weightedIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem normalizedHaar_scalarLattice_eq_localDeg_product_general
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.normalizedHaar (P.scalarLattice z) =
      ENNReal.ofReal (∏ i, ‖z i‖ ^
        FiniteTensorMatrix.otherDimension (fun j => Arithmetic.localDeg (P.place j)) i) := by
  rw [P.normalizedHaar_scalarLattice_eq_factorNorm_product z hz]
  simp only [P.factor_finrank_eq_localDeg]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [LocalCompletion.norm_algebraNorm_eq_completionNorm
    (P.place i) (P.residueChar_eq i) (z i) (hz i)]

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

theorem degreeLogVolume_scalarLattice_eq_norm_sum_general
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.degreeLogVolume (P.scalarLattice z) =
      ∑ i, Real.log ‖z i‖ / (Arithmetic.localDeg (P.place i) : ℝ) := by
  rw [degreeLogVolume, P.normalizedHaar_scalarLattice_eq_localDeg_product_general z hz,
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

theorem degreeVolume_scalarLattice_eq_norm_product_general
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.degreeVolume (P.scalarLattice z) =
      ∏ i, ‖z i‖ ^ (1 / (Arithmetic.localDeg (P.place i) : ℝ)) := by
  have hS : 0 < (P.normalizedHaar (P.scalarLattice z)).toReal := by
    rw [P.normalizedHaar_scalarLattice_eq_localDeg_product_general z hz,
      ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)]
    exact Finset.prod_pos fun i _ => pow_pos (norm_pos_iff.mpr (hz i)) _
  rw [P.degreeVolume_eq_exp_degreeLogVolume _ hS,
    P.degreeLogVolume_scalarLattice_eq_norm_sum_general z hz, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (hz i))]
  congr 1
  ring

/-- A function of the actual tensor region, with a common weighted degree. -/
def weightedRegionVolume (c : ℝ) (S : Set P.Tensor) : ℝ :=
  Real.exp (c * P.degreeLogVolume S)

theorem weightedRegionVolume_scalarLattice
    (γ : ι → ℝ) (c : ℝ)
    (hγ : ∀ i, (Arithmetic.localDeg (P.place i) : ℝ) * γ i = c)
    (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0) :
    P.weightedRegionVolume c (P.scalarLattice z) = P.weightedScalarVolume γ z := by
  rw [weightedRegionVolume, P.degreeLogVolume_scalarLattice_eq_norm_sum_general z hz,
    Finset.mul_sum, Real.exp_sum, weightedScalarVolume]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (hz i))]
  congr 1
  rw [← hγ i]
  have hd : (Arithmetic.localDeg (P.place i) : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.localDeg_pos _).ne'
  field_simp
  <;> ring

/-- Descent is equivalent to a common weighted degree, for all nonzero
scalar presentations, including units and expanding factors. -/
theorem exists_weighted_region_volume_iff (γ : ι → ℝ) :
    (∃ V : Submodule ℤ_[p] P.Tensor → ℝ,
      ∀ (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0),
        V (P.scalarLattice z) = P.weightedScalarVolume γ z) ↔
      ∃ c : ℝ, ∀ i, (Arithmetic.localDeg (P.place i) : ℝ) * γ i = c := by
  constructor
  · rintro ⟨V, hV⟩
    by_cases hι : Nonempty ι
    · let i := Classical.choice hι
      refine ⟨(Arithmetic.localDeg (P.place i) : ℝ) * γ i, ?_⟩
      intro j
      exact P.weightedDegree_eq_of_prime_region_volume γ V
        (fun k => hV _ (P.primeAtScalar_ne_zero k)) j i
    · exact ⟨0, fun i => False.elim (hι ⟨i⟩)⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun S => P.weightedRegionVolume c S,
      fun z hz => P.weightedRegionVolume_scalarLattice γ c hc z hz⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
