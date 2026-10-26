import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusDynamics
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialLinearization

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-INVERSE-RADIUS-ORBIT
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the radius
family under inverse Frobenius on the actual period algebra.
fidelity: constructs rho^(p^(-n)) in the original radius type, proves
the exact powered-radius relation and convergence to one, and brackets
every radius above rho by two adjacent orbit radii.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; these are the original radii. No comparison
map, exponential convergence or period representation is input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittInverseRadiusOrbit

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittRhoFrobeniusCompletion
open InitialThetaWittExponentialSeries InitialThetaWittExponentialLinearization
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def orbit (ρ : Radius) (n : ℕ) : Radius :=
  ⟨ρ.val ^ (((Arithmetic.residueChar w.1 : ℝ)⁻¹) ^ n),
    ENNReal.rpow_pos ρ.property.1 (ρ.property.2.trans ENNReal.one_lt_top).ne,
    ENNReal.rpow_lt_one ρ.property.2 (pow_pos (inv_pos.mpr
      (Nat.cast_pos.mpr (Arithmetic.residueChar_prime w.1).pos)) n)⟩

theorem orbit_zero (ρ : Radius) : orbit D w ρ 0 = ρ := by
  apply Subtype.ext
  simp only [orbit, pow_zero, ENNReal.rpow_one]

theorem powered_orbit_succ (ρ : Radius) (n : ℕ) :
    poweredRadius D w (orbit D w ρ (n + 1)) = orbit D w ρ n := by
  apply Subtype.ext
  change (ρ.val ^ (((Arithmetic.residueChar w.1 : ℝ)⁻¹) ^ (n + 1))) ^ Arithmetic.residueChar w.1 = _
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, pow_succ, mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero), mul_one]
  rfl

theorem orbit_toReal_pow (ρ : Radius) (n : ℕ) :
    (orbit D w ρ (n + 1)).val.toReal ^ Arithmetic.residueChar w.1 = (orbit D w ρ n).val.toReal := by
  have h := congrArg (fun r : Radius => r.val.toReal) (powered_orbit_succ D w ρ n)
  simpa only [poweredRadius, ENNReal.toReal_pow] using h

theorem orbit_toReal_tendsto_one (ρ : Radius) :
    Filter.Tendsto (fun n : ℕ => (orbit D w ρ n).val.toReal) Filter.atTop (𝓝 1) := by
  have hp : (1 : ℝ) < Arithmetic.residueChar w.1 := by
    exact_mod_cast (Arithmetic.residueChar_prime w.1).one_lt
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (le_of_lt (zero_lt_one.trans hp)))
    (inv_lt_one_of_one_lt₀ hp)
  have ht := (Real.continuous_const_rpow (radius_toReal_pos ρ).ne').continuousAt.tendsto.comp h
  simpa only [orbit, ← ENNReal.toReal_rpow, Real.rpow_zero, Function.comp_def] using ht

theorem exists_orbit_above (ρ s : Radius) : ∃ n : ℕ, s.val.toReal < (orbit D w ρ n).val.toReal :=
  ((orbit_toReal_tendsto_one D w ρ).eventually (lt_mem_nhds (radius_toReal_lt_one s))).exists

theorem exists_adjacent_bracket (ρ s : Radius) (hρs : ρ.val ≤ s.val) : ∃ n : ℕ,
    (orbit D w ρ n).val ≤ s.val ∧ s.val ≤ (orbit D w ρ (n + 1)).val := by
  have h := exists_orbit_above D w ρ s
  have hm := Nat.find_spec h
  have hm0 : Nat.find h ≠ 0 := by
    intro he
    rw [he, orbit_zero] at hm
    have hle := (ENNReal.toReal_le_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne
      (s.property.2.trans ENNReal.one_lt_top).ne).mpr hρs
    exact (not_lt_of_ge hle) hm
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨n, ?_, ?_⟩
  · have hl : (orbit D w ρ n).val.toReal ≤ s.val.toReal :=
      le_of_not_gt (Nat.find_min h (by omega : n < Nat.find h))
    exact (ENNReal.toReal_le_toReal ((orbit D w ρ n).property.2.trans ENNReal.one_lt_top).ne
      (s.property.2.trans ENNReal.one_lt_top).ne).mp hl
  · rw [hn] at hm
    exact (ENNReal.toReal_le_toReal (s.property.2.trans ENNReal.one_lt_top).ne
      ((orbit D w ρ (n + 1)).property.2.trans ENNReal.one_lt_top).ne).mp hm.le

end
end JoshiTeich.Act1Scene1.InitialThetaWittInverseRadiusOrbit
