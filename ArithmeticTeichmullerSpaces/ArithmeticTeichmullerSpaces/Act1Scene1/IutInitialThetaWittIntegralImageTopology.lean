import ArithmeticTeichmullerSpaces.Act1Scene1.WittCoefficientConvergence
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCoefficientLimits

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-INTEGRAL-IMAGE-TOPOLOGY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, topology
on the actual integral Witt source inside the rho completions.
fidelity: coefficient convergence in the original tilt field makes
each digit norm of the actual Witt difference tend to zero. Finite
digit heads and the uniform rho^(N+1) remainder bound then prove
convergence of the same original rho images, at every radius.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no integral image closedness, reconstruction
law or period representation is assumed. Original norms retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittIntegralImageTopology

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open WittTeichmullerExpansion InitialThetaBoundedWittExpansion
open InitialThetaWittExponentialSeries
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem tendsto_norm_digits_sub (a : ℕ → InitialThetaTiltFontaine.Ainf D w)
    (b : InitialThetaTiltFontaine.Ainf D w)
    (ha : ∀ i : ℕ, Filter.Tendsto (fun m => ((a m).coeff i : InitialThetaTiltField.Carrier D w))
      Filter.atTop (𝓝 (b.coeff i : InitialThetaTiltField.Carrier D w))) (i : ℕ) :
    Filter.Tendsto (fun m => ‖digits (Arithmetic.residueChar w.1) (a m - b) i‖) Filter.atTop (𝓝 0) := by
  have ha' : ∀ j : ℕ, Filter.Tendsto (fun m => (wittInclusion D w (a m)).coeff j)
      Filter.atTop (𝓝 ((wittInclusion D w b).coeff j)) := ha
  have ht := WittCoefficientConvergence.tendsto_sub_coeff (Arithmetic.residueChar w.1)
    (fun m => wittInclusion D w (a m)) (wittInclusion D w b) ha' i
  have he (m : ℕ) : ‖(wittInclusion D w (a m) - wittInclusion D w b).coeff i‖ =
      ‖digits (Arithmetic.residueChar w.1) (a m - b) i‖ ^ (Arithmetic.residueChar w.1 ^ i) := by
    rw [← map_sub]
    change ‖(a m - b).coeff i‖ = _
    rw [(expands_iff_coeff (Arithmetic.residueChar w.1) (a m - b) _).mp
      (expands_digits _ (a m - b)) i, norm_pow]
  apply (PositivePowerCalibration.tendsto_rpow_zero_iff Filter.atTop
    (fun m => ‖digits (Arithmetic.residueChar w.1) (a m - b) i‖) (fun _ => norm_nonneg _)
    ((Arithmetic.residueChar w.1 ^ i : ℕ) : ℝ)
    (Nat.cast_pos.mpr (pow_pos (Arithmetic.residueChar_prime w.1).pos i))).mp
  simpa only [Real.rpow_natCast, ← he, norm_zero] using ht.norm

theorem norm_partial_le_of_head (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w)
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hhead : ∀ i ≤ N, ‖digits (Arithmetic.residueChar w.1) a i‖ * ρ.val.toReal ^ i ≤ B) :
    ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (InitialThetaWittRhoExpansion.digitPartialSum D w a N)‖ ≤ B := by
  unfold InitialThetaWittRhoExpansion.digitPartialSum partialSum
  rw [map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB
  intro i hi
  rw [map_mul, map_pow, norm_mul, norm_pow, InitialThetaWittTateLogarithm.norm_ainf_teichmuller,
    InitialThetaWittRhoExpansion.norm_ainfMap_prime]
  exact hhead i (Finset.mem_Iic.mp hi)

theorem norm_image_le_of_head_tail (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w)
    (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hhead : ∀ i ≤ N, ‖digits (Arithmetic.residueChar w.1) a i‖ * ρ.val.toReal ^ i ≤ B)
    (htail : ρ.val.toReal ^ (N + 1) ≤ B) : ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ ≤ B := by
  let v := InitialThetaWittRhoExpansion.ainfMap D w ρ (InitialThetaWittRhoExpansion.digitPartialSum D w a N)
  calc
    _ = ‖(InitialThetaWittRhoExpansion.ainfMap D w ρ a - v) + v‖ := by rw [sub_add_cancel]
    _ ≤ max ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a - v‖ ‖v‖ :=
      InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _
    _ ≤ B := max_le ((InitialThetaWittRhoExpansion.norm_remainder_le D w ρ a N).trans htail)
      (norm_partial_le_of_head D w ρ a N B hB hhead)

theorem tendsto_ainfMap_of_coeff (ρ : Radius) (a : ℕ → InitialThetaTiltFontaine.Ainf D w)
    (b : InitialThetaTiltFontaine.Ainf D w)
    (ha : ∀ i : ℕ, Filter.Tendsto (fun m => ((a m).coeff i : InitialThetaTiltField.Carrier D w))
      Filter.atTop (𝓝 (b.coeff i : InitialThetaTiltField.Carrier D w))) :
    Filter.Tendsto (fun m => InitialThetaWittRhoExpansion.ainfMap D w ρ (a m)) Filter.atTop
      (𝓝 (InitialThetaWittRhoExpansion.ainfMap D w ρ b)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (radius_toReal_pos ρ).le
    (InitialThetaWittExponentialLinearization.radius_toReal_lt_one ρ)
  have ht : Filter.Tendsto (fun N : ℕ => ρ.val.toReal ^ (N + 1)) Filter.atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using hp.mul_const ρ.val.toReal
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  have hh : ∀ᶠ m : ℕ in Filter.atTop, ∀ i ∈ Finset.Iic N,
      ‖digits (Arithmetic.residueChar w.1) (a m - b) i‖ * ρ.val.toReal ^ i ≤ ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hd := (tendsto_norm_digits_sub D w a b ha i).mul_const (ρ.val.toReal ^ i)
    rw [zero_mul] at hd
    exact (hd.eventually (gt_mem_nhds (half_pos hε))).mono (fun _ h => h.le)
  filter_upwards [hh] with m hm
  have hb := norm_image_le_of_head_tail D w ρ (a m - b) N (ε / 2) (half_pos hε).le
    (fun i hi => hm i (Finset.mem_Iic.mpr hi)) hN.le
  simpa only [dist_zero_right, norm_norm, ← map_sub] using hb.trans_lt (half_lt_self hε)

end
end JoshiTeich.Act1Scene1.InitialThetaWittIntegralImageTopology
