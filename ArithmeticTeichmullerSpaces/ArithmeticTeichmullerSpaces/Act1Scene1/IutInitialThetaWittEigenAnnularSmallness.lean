import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittInverseRadiusOrbit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-ANNULAR-SMALLNESS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, recognition
of multiplicative-formal-group periods in the full phi=p subspace.
fidelity: the actual eigen norm recursion propagates N_rho(z)<rho^(p+1)
along the inverse Frobenius radius orbit. Adjacent endpoint interpolation
then proves N_s(z)<s at every s>=rho. Every full eigen element acquires
this entire annular convergence domain after one actual p-power scaling.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; retains the full eigenspace and original
coordinate norms. No Teichmuller representative or uniform convergence
near radius one is assumed or asserted. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenAnnularSmallness

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittEigenRadiusDynamics InitialThetaWittInverseRadiusOrbit
open InitialThetaWittExponentialSeries InitialThetaWittExponentialLinearization
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem coordinate_orbit_lt (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val <
      ρ.val.toReal ^ (Arithmetic.residueChar w.1 + 1)) (n : ℕ) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w (orbit D w ρ n) z.val <
      (orbit D w ρ n).val.toReal ^ (Arithmetic.residueChar w.1 + 1) := by
  induction n with
  | zero => simpa only [orbit_zero] using hz
  | succ n ih =>
    apply lt_of_pow_lt_pow_left₀ (Arithmetic.residueChar w.1)
      (pow_nonneg (radius_toReal_pos (orbit D w ρ (n + 1))).le _)
    rw [coordinate_powered, powered_orbit_succ]
    calc
      _ ≤ InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w (orbit D w ρ n) z.val :=
        mul_le_of_le_one_left (norm_nonneg (InitialThetaWittAllRadiusCompletion.evaluate D w _ z.val))
          (radius_toReal_lt_one (orbit D w ρ n)).le
      _ < (orbit D w ρ n).val.toReal ^ (Arithmetic.residueChar w.1 + 1) := ih
      _ = _ := by rw [← orbit_toReal_pow D w ρ n, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem coordinate_orbit_lt_radius (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val <
      ρ.val.toReal ^ (Arithmetic.residueChar w.1 + 1)) (n : ℕ) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w (orbit D w ρ n) z.val <
      (orbit D w ρ n).val.toReal := by
  have h := coordinate_orbit_lt D w ρ z hz n
  have hp := pow_le_pow_of_le_one (radius_toReal_pos (orbit D w ρ n)).le
    (radius_toReal_lt_one (orbit D w ρ n)).le (Nat.le_add_left 1 (Arithmetic.residueChar w.1))
  exact h.trans_le (by simpa only [pow_one] using hp)

theorem coordinate_next_lt_previous_radius (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val <
      ρ.val.toReal ^ (Arithmetic.residueChar w.1 + 1)) (n : ℕ) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w (orbit D w ρ (n + 1)) z.val <
      (orbit D w ρ n).val.toReal := by
  rw [← orbit_toReal_pow D w ρ n]
  exact (coordinate_orbit_lt D w ρ z hz (n + 1)).trans_le
    (pow_le_pow_of_le_one (radius_toReal_pos (orbit D w ρ (n + 1))).le
      (radius_toReal_lt_one (orbit D w ρ (n + 1))).le (Nat.le_succ (Arithmetic.residueChar w.1)))

theorem coordinate_lt_radius_of_le (ρ : Radius) (z : Eigen D w)
    (hz : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val <
      ρ.val.toReal ^ (Arithmetic.residueChar w.1 + 1)) (s : Radius) (hρs : ρ.val ≤ s.val) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w s z.val < s.val.toReal := by
  obtain ⟨n, hn, hn'⟩ := exists_adjacent_bracket D w ρ s hρs
  have h := InitialThetaWittRadiusInterpolation.coordinateSeminorm_le_endpoint_max D w
    (orbit D w ρ n) s (orbit D w ρ (n + 1)) hn hn' z.val
  exact (h.trans_lt (max_lt (coordinate_orbit_lt_radius D w ρ z hz n)
    (coordinate_next_lt_previous_radius D w ρ z hz n))).trans_le
      ((ENNReal.toReal_le_toReal ((orbit D w ρ n).property.2.trans ENNReal.one_lt_top).ne
        (s.property.2.trans ENNReal.one_lt_top).ne).mpr hn)

theorem exists_prime_pow_smul_bound (ρ : Radius) (z : Eigen D w) : ∃ k : ℕ,
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val <
        ρ.val.toReal ^ (Arithmetic.residueChar w.1 + 1) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (radius_toReal_pos ρ).le
    (radius_toReal_lt_one ρ)).mul_const
      (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ z.val)
  rw [zero_mul] at h
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds
    (pow_pos (radius_toReal_pos ρ) (Arithmetic.residueChar w.1 + 1)))).exists
  refine ⟨k, ?_⟩
  change InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
    (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z.val) < _
  rw [InitialThetaWittPadicScalarNorm.coordinateSeminorm_smul, map_pow, map_natCast, norm_pow,
    InitialThetaWittPadicScalarContinuity.norm_completed_prime]
  exact hk

theorem exists_prime_pow_smul_annular (ρ : Radius) (z : Eigen D w) : ∃ k : ℕ,
    ∀ s : Radius, ρ.val ≤ s.val → InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w s
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val < s.val.toReal := by
  obtain ⟨k, hk⟩ := exists_prime_pow_smul_bound D w ρ z
  exact ⟨k, coordinate_lt_radius_of_le D w ρ _ hk⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenAnnularSmallness
