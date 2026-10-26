import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAdditiveTatePeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRadiusFaithfulness

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-RADIUS-DYNAMICS
source: Joshi II `se:ff-rings` and the B^{phi=p} period sequence in
the proof of `pr:teichmuller-lift-A`.
fidelity: on the entire actual phi=p subspace, computes the radius-power
norm recursion from the original Frobenius and scalar norm laws. Iterated
powered radii approach zero and preserve zero-convergence detection in
both directions. No principal-log representation is assumed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the original common ring and eigen subspace
topologies are retained. Full period/BK identity remains open. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenRadiusDynamics

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusCompletion InitialThetaWittAdditiveTatePeriod
open InitialThetaWittRhoFrobeniusCompletion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Eigen := frobeniusPrimeSubmodule D w

def radiusOrbit (ρ : Radius) : ℕ → Radius
  | 0 => ρ
  | n + 1 => poweredRadius D w (radiusOrbit ρ n)

theorem radiusOrbit_val (ρ : Radius) (n : ℕ) :
    (radiusOrbit D w ρ n).val = ρ.val ^ (Arithmetic.residueChar w.1 ^ n) := by
  induction n with
  | zero => simp only [radiusOrbit, pow_zero, pow_one]
  | succ n ih =>
    change (radiusOrbit D w ρ n).val ^ Arithmetic.residueChar w.1 = _
    rw [ih, pow_succ, pow_mul]

theorem radiusOrbit_toReal_tendsto_zero (ρ : Radius) :
    Filter.Tendsto (fun n : ℕ => (radiusOrbit D w ρ n).val.toReal) Filter.atTop (𝓝 0) := by
  have hr : ρ.val.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr
        ρ.property.2
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hr).comp
    (tendsto_pow_atTop_atTop_of_one_lt (Arithmetic.residueChar_prime w.1).one_lt)
  simpa only [radiusOrbit_val, ENNReal.toReal_pow, Function.comp_def] using h

theorem exists_radiusOrbit_le (ρ s : Radius) : ∃ n : ℕ, (radiusOrbit D w ρ n).val ≤ s.val := by
  have hs : 0 < s.val.toReal :=
    ENNReal.toReal_pos s.property.1.ne' (s.property.2.trans ENNReal.one_lt_top).ne
  obtain ⟨n, hn⟩ := ((radiusOrbit_toReal_tendsto_zero D w ρ).eventually (gt_mem_nhds hs)).exists
  exact ⟨n, (ENNReal.toReal_le_toReal
    ((radiusOrbit D w ρ n).property.2.trans ENNReal.one_lt_top).ne
    (s.property.2.trans ENNReal.one_lt_top).ne).mp hn.le⟩

theorem coordinate_powered (ρ : Radius) (x : Eigen D w) :
    coordinateSeminorm D w ρ x.val ^ Arithmetic.residueChar w.1 =
      (poweredRadius D w ρ).val.toReal * coordinateSeminorm D w (poweredRadius D w ρ) x.val := by
  have he : InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x.val =
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x.val := x.property
  have h := InitialThetaWittAllRadiusFrobenius.coordinateSeminorm_frobenius D w ρ x.val
  rw [he, InitialThetaWittPadicScalarNorm.coordinateSeminorm_smul, map_natCast] at h
  have hp := InitialThetaWittScalarPrimeScaling.norm_mul_prime D w (poweredRadius D w ρ)
    (1 : InitialThetaWittRhoCompletion.Completed D w (poweredRadius D w ρ))
  simp only [one_mul, norm_one, mul_one] at hp
  rw [hp] at h
  exact h.symm

theorem coordinate_powered_eq (ρ : Radius) (x : Eigen D w) :
    coordinateSeminorm D w (poweredRadius D w ρ) x.val =
      coordinateSeminorm D w ρ x.val ^ Arithmetic.residueChar w.1 /
        (poweredRadius D w ρ).val.toReal := by
  apply (eq_div_iff (ENNReal.toReal_pos (poweredRadius D w ρ).property.1.ne'
    ((poweredRadius D w ρ).property.2.trans ENNReal.one_lt_top).ne).ne').mpr
  simpa only [mul_comm] using (coordinate_powered D w ρ x).symm

theorem tendsto_powered_iff {ι : Type*} (l : Filter ι) (f : ι → Eigen D w) (ρ : Radius) :
    Filter.Tendsto (fun i => coordinateSeminorm D w (poweredRadius D w ρ) (f i).val) l (𝓝 0) ↔
      Filter.Tendsto (fun i => coordinateSeminorm D w ρ (f i).val) l (𝓝 0) := by
  constructor
  · intro h
    apply (PositivePowerCalibration.tendsto_rpow_zero_iff l
      (fun i => coordinateSeminorm D w ρ (f i).val)
      (fun i => apply_nonneg _ _) (Arithmetic.residueChar w.1 : ℝ)
      (Nat.cast_pos.mpr (Arithmetic.residueChar_prime w.1).pos)).mp
    have ht : Filter.Tendsto (fun i => (poweredRadius D w ρ).val.toReal *
        coordinateSeminorm D w (poweredRadius D w ρ) (f i).val) l
        (𝓝 ((poweredRadius D w ρ).val.toReal * 0)) := tendsto_const_nhds.mul h
    simpa only [Real.rpow_natCast, coordinate_powered, mul_zero] using ht
  · intro h
    have ht := (h.pow (Arithmetic.residueChar w.1)).div_const (poweredRadius D w ρ).val.toReal
    simpa only [coordinate_powered_eq, zero_pow (Arithmetic.residueChar_prime w.1).ne_zero,
      zero_div] using ht

theorem tendsto_radiusOrbit_iff {ι : Type*} (l : Filter ι) (f : ι → Eigen D w)
    (ρ : Radius) (n : ℕ) :
    Filter.Tendsto (fun i => coordinateSeminorm D w (radiusOrbit D w ρ n) (f i).val) l (𝓝 0) ↔
      Filter.Tendsto (fun i => coordinateSeminorm D w ρ (f i).val) l (𝓝 0) := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    rw [radiusOrbit, tendsto_powered_iff]
    exact ih

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenRadiusDynamics
