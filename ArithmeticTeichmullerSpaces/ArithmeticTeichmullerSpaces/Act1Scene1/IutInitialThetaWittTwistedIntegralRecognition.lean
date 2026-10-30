import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittCompletedIntegralCriterion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelSimpleZero
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittInverseRadiusOrbit

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TWISTED-INTEGRAL-RECOGNITION
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, integral recognition of actual period solutions.
fidelity: every original full common-ring solution phi(x)=-xi*x becomes
an image of original Ainf after multiplication by a constructed p^N.
The small-radius norm bound propagates down the powered-radius orbit;
the large-radius unit bound propagates up the inverse-radius orbit.
One p-power gives both starting bounds. Endpoint interpolation gives
all original unit bounds, and the proved completed unit-ball criterion
constructs the integral Witt representative. Original Frobenius
compatibility proves its actual Witt equation as well.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no bounded or integral representative is
an input. This concerns the full original common carrier. Rational
classification of these integral solutions, the full Tate-kernel
identity and paper period/BK comparisons remain open. R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTwistedIntegralRecognition

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius InitialThetaWittRhoFrobeniusCompletion
open InitialThetaWittThetaPrincipalKernel InitialThetaWittFrobeniusThetaOrbit
open InitialThetaWittNormalizedOrbitProduct InitialThetaWittMultiplicativeNorm
open InitialThetaWittExponentialSeries InitialThetaWittExponentialLinearization
open InitialThetaWittEigenRadiusDynamics InitialThetaWittInverseRadiusOrbit
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

theorem primitive_large_radius_norm (r : Radius) (hr : primeNorm D w < r.val.toReal) :
    coordinateSeminorm D w r (primitive D w) = r.val.toReal := by
  have hp : ‖evaluate D w r (Arithmetic.residueChar w.1 : Carrier D w)‖ = r.val.toReal := by
    simpa only [map_natCast] using InitialThetaWittRhoCompletion.inclusion_prime_norm D w r
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (x := evaluate D w r (teichPrime D w))
    (y := -evaluate D w r (Arithmetic.residueChar w.1 : Carrier D w))
    (by rw [norm_neg, norm_evaluate_teichPrime, hp]; exact ne_of_lt hr)
  change ‖evaluate D w r (primitive D w)‖ = _
  rw [primitive_eq_teichPrime_sub, map_sub]
  simpa only [← sub_eq_add_neg, norm_neg, norm_evaluate_teichPrime, hp, max_eq_right hr.le] using h

private theorem powered_toReal_le (r : Radius) :
    (poweredRadius D w r).val.toReal ≤ r.val.toReal := by
  change (r.val ^ Arithmetic.residueChar w.1).toReal ≤ _
  rw [ENNReal.toReal_pow]
  simpa only [pow_one] using pow_le_pow_of_le_one (radius_toReal_pos r).le
    (radius_toReal_lt_one r).le (Arithmetic.residueChar_prime w.1).pos

private theorem coordinate_twisted (r : Radius) (x : Carrier D w)
    (hx : frobeniusEquiv D w x = -primitive D w * x) :
    coordinateSeminorm D w r x ^ Arithmetic.residueChar w.1 =
      coordinateSeminorm D w (poweredRadius D w r) (primitive D w) *
        coordinateSeminorm D w (poweredRadius D w r) x := by
  have h := coordinateSeminorm_frobenius D w r x
  change ‖evaluate D w (poweredRadius D w r) (frobeniusEquiv D w x)‖ = _ at h
  rw [hx, map_mul, map_neg, norm_mul, norm_neg] at h
  exact h.symm

private theorem forward_bounds (r : Radius) (hr : r.val.toReal < primeNorm D w)
    (x : Carrier D w) (hx : frobeniusEquiv D w x = -primitive D w * x)
    (hbound : coordinateSeminorm D w r x ≤ primeNorm D w) :
    ∀ n : ℕ, coordinateSeminorm D w (radiusOrbit D w r n) x ≤ primeNorm D w := by
  have hrad (n : ℕ) : (radiusOrbit D w r n).val.toReal ≤ r.val.toReal := by
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (powered_toReal_le D w _).trans ih
  intro n
  induction n with
  | zero => exact hbound
  | succ n ih =>
    have hsmall : (poweredRadius D w (radiusOrbit D w r n)).val.toReal < primeNorm D w :=
      ((powered_toReal_le D w _).trans (hrad n)).trans_lt hr
    have he := coordinate_twisted D w (radiusOrbit D w r n) x hx
    rw [InitialThetaWittEigenKernelSimpleZero.primitive_small_radius_norm D w _ hsmall] at he
    change coordinateSeminorm D w (poweredRadius D w (radiusOrbit D w r n)) x ≤ _
    apply (mul_le_mul_iff_right₀ (primeNorm_pos_lt_one D w).1).mp
    rw [← he]
    calc
      _ ≤ primeNorm D w ^ Arithmetic.residueChar w.1 := pow_le_pow_left₀ (apply_nonneg _ _) ih _
      _ ≤ primeNorm D w ^ 2 := pow_le_pow_of_le_one (primeNorm_pos_lt_one D w).1.le
        (primeNorm_pos_lt_one D w).2.le (Arithmetic.residueChar_prime w.1).two_le
      _ = _ := pow_two _

private theorem inverse_bounds (r : Radius) (hr : primeNorm D w < r.val.toReal)
    (x : Carrier D w) (hx : frobeniusEquiv D w x = -primitive D w * x)
    (hbound : coordinateSeminorm D w r x ≤ 1) :
    ∀ n : ℕ, coordinateSeminorm D w (orbit D w r n) x ≤ 1 := by
  have hstep (n : ℕ) : (orbit D w r n).val.toReal ≤ (orbit D w r (n + 1)).val.toReal := by
    have h := powered_toReal_le D w (orbit D w r (n + 1))
    rw [powered_orbit_succ] at h
    exact h
  have hrad (n : ℕ) : r.val.toReal ≤ (orbit D w r n).val.toReal := by
    induction n with
    | zero => rw [orbit_zero]
    | succ n ih => exact ih.trans (hstep n)
  intro n
  induction n with
  | zero => simpa only [orbit_zero] using hbound
  | succ n ih =>
    have he := coordinate_twisted D w (orbit D w r (n + 1)) x hx
    rw [powered_orbit_succ, primitive_large_radius_norm D w _ (hr.trans_le (hrad n))] at he
    apply le_of_pow_le_pow_left₀ (Arithmetic.residueChar_prime w.1).ne_zero (by norm_num : (0 : ℝ) ≤ 1)
    rw [one_pow, he]
    exact (mul_le_of_le_one_right (radius_toReal_pos _).le ih).trans (radius_toReal_lt_one _).le

private theorem prime_pow_twisted (N : ℕ) (x : Carrier D w)
    (hx : frobeniusEquiv D w x = -primitive D w * x) :
    frobeniusEquiv D w ((Arithmetic.residueChar w.1 : Carrier D w) ^ N * x) =
      -primitive D w * ((Arithmetic.residueChar w.1 : Carrier D w) ^ N * x) := by
  rw [map_mul, map_pow, map_natCast, hx]
  ring

private theorem coordinate_prime_pow_mul (r : Radius) (N : ℕ) (x : Carrier D w) :
    coordinateSeminorm D w r ((Arithmetic.residueChar w.1 : Carrier D w) ^ N * x) =
      r.val.toReal ^ N * coordinateSeminorm D w r x := by
  change ‖evaluate D w r ((Arithmetic.residueChar w.1 : Carrier D w) ^ N * x)‖ = _
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow,
    InitialThetaWittPadicScalarContinuity.norm_completed_prime]
  rfl

theorem exists_prime_pow_unit_bounds (x : Carrier D w)
    (hx : frobeniusEquiv D w x = -primitive D w * x) :
    ∃ N : ℕ, ∀ r : Radius,
      coordinateSeminorm D w r ((Arithmetic.residueChar w.1 : Carrier D w) ^ N * x) ≤ 1 := by
  let r₀ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  obtain ⟨i, hi⟩ := ((radiusOrbit_toReal_tendsto_zero D w r₀).eventually
    (gt_mem_nhds (primeNorm_pos_lt_one D w).1)).exists
  obtain ⟨j, hj⟩ := ((orbit_toReal_tendsto_one D w r₀).eventually
    (lt_mem_nhds (primeNorm_pos_lt_one D w).2)).exists
  let a := radiusOrbit D w r₀ i
  let b := orbit D w r₀ j
  have hlim (r : Radius) : Filter.Tendsto (fun N : ℕ => r.val.toReal ^ N * coordinateSeminorm D w r x)
      Filter.atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (radius_toReal_pos r).le
      (radius_toReal_lt_one r)).mul_const (coordinateSeminorm D w r x)
    simpa only [zero_mul] using h
  obtain ⟨N, hNa, hNb⟩ := ((hlim a).eventually (gt_mem_nhds (primeNorm_pos_lt_one D w).1) |>.and
    ((hlim b).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))).exists
  let z := (Arithmetic.residueChar w.1 : Carrier D w) ^ N * x
  have hz : frobeniusEquiv D w z = -primitive D w * z := prime_pow_twisted D w N x hx
  have ha : coordinateSeminorm D w a z ≤ primeNorm D w := by
    rw [coordinate_prime_pow_mul]
    exact hNa.le
  have hb : coordinateSeminorm D w b z ≤ 1 := by
    rw [coordinate_prime_pow_mul]
    exact hNb.le
  have hdown := forward_bounds D w a hi z hz ha
  have hup := inverse_bounds D w b hj z hz hb
  refine ⟨N, fun r => ?_⟩
  obtain ⟨m, hm⟩ := exists_radiusOrbit_le D w a r
  obtain ⟨n, hn⟩ := exists_orbit_above D w b r
  have hn' : r.val ≤ (orbit D w b n).val :=
    (ENNReal.toReal_le_toReal (r.property.2.trans ENNReal.one_lt_top).ne
      ((orbit D w b n).property.2.trans ENNReal.one_lt_top).ne).mp hn.le
  exact (InitialThetaWittRadiusInterpolation.coordinateSeminorm_le_endpoint_max D w
    (radiusOrbit D w a m) r (orbit D w b n) hm hn' z).trans
      (max_le ((hdown m).trans (primeNorm_pos_lt_one D w).2.le) (hup n))

theorem exists_integral_prime_pow (x : Carrier D w)
    (hx : frobeniusEquiv D w x = -primitive D w * x) :
    ∃ N : ℕ, ∃ a : InitialThetaTiltFontaine.Ainf D w,
      InitialThetaWittAllRadiusExpansion.ainfMap D w a =
        (Arithmetic.residueChar w.1 : Carrier D w) ^ N * x ∧
      WittVector.frobenius a = -InitialThetaTiltFontaine.primitive D w * a := by
  obtain ⟨N, hN⟩ := exists_prime_pow_unit_bounds D w x hx
  let r₀ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  let z := (Arithmetic.residueChar w.1 : Carrier D w) ^ N * x
  obtain ⟨a, ha⟩ := InitialThetaWittCompletedIntegralCriterion.exists_integral_of_unit_bounds
    D w r₀ z hN
  refine ⟨N, a, ha, ?_⟩
  apply InitialThetaWittTeichmullerRecognition.ainfMap_injective D w (poweredRadius D w r₀)
  rw [← InitialThetaWittTeichmullerRecognition.completedFrobenius_ainfMap]
  have ha' : InitialThetaWittAllRadiusExpansion.ainfMap D w a =
      (Arithmetic.residueChar w.1 : Carrier D w) ^ N * x := ha
  have hf := (evaluate_frobenius D w r₀ z).symm
  dsimp only [z] at hf
  rw [prime_pow_twisted D w N x hx] at hf
  simp only [← ha'] at hf
  calc
    _ = evaluate D w (poweredRadius D w r₀)
        (-primitive D w * InitialThetaWittAllRadiusExpansion.ainfMap D w a) := hf
    _ = _ := by
      rw [map_mul, map_neg, map_mul, map_neg]
      rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittTwistedIntegralRecognition
