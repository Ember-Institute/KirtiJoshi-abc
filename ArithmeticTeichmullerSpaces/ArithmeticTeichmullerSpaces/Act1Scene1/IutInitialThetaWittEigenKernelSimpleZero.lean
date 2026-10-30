import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrobeniusWeight
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenKernelFirstOrder
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTwistedTatePeriod

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-KERNEL-SIMPLE-ZERO
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, primitive zeros of actual Frobenius periods.
fidelity: propagates squared primitive divisibility along the actual
Frobenius orbit. Coprimality and multiplicative-norm division construct
a quotient by the square of the original normalized orbit product.
The quotient satisfies p*phi(y)=xi^2*y. At small original radii the
primitive norm is constant, so this equation contradicts logarithmic
norm convexity unless y=0. Thus a nonzero phi=p element has no double
primitive zero, and the existing first-order kernel evaluation is
injective. Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no t^2 divisibility bridge is assumed.
This proves simple primitive zeros, not the rational dimension or full
Tate-kernel identity. Original carriers and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelSimpleZero

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius InitialThetaWittRhoFrobeniusCompletion
open InitialThetaWittEigenRadiusDynamics InitialThetaWittThetaPrincipalKernel
open InitialThetaWittFrobeniusThetaOrbit InitialThetaWittNormalizedOrbitProduct
open InitialThetaWittEigenKernelFiniteDivision InitialThetaWittEigenKernelInfiniteDivision
open InitialThetaWittMultiplicativeNorm InitialThetaWittExponentialSeries
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

private theorem coordinate_pos (r : Radius) (x : Carrier D w) (hx : x ≠ 0) :
    0 < coordinateSeminorm D w r x := by
  exact lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm fun h =>
    hx ((InitialThetaWittRadiusFaithfulness.coordinateSeminorm_eq_zero_iff D w r x).mp h))

theorem primitive_small_radius_norm (r : Radius) (hr : r.val.toReal < primeNorm D w) :
    coordinateSeminorm D w r (primitive D w) = primeNorm D w := by
  have hp : ‖evaluate D w r (Arithmetic.residueChar w.1 : Carrier D w)‖ = r.val.toReal := by
    simpa only [map_natCast] using InitialThetaWittRhoCompletion.inclusion_prime_norm D w r
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (x := evaluate D w r (teichPrime D w))
    (y := -evaluate D w r (Arithmetic.residueChar w.1 : Carrier D w))
    (by rw [norm_neg, norm_evaluate_teichPrime, hp]; exact ne_of_gt hr)
  change ‖evaluate D w r (primitive D w)‖ = _
  rw [primitive_eq_teichPrime_sub, map_sub]
  simpa only [← sub_eq_add_neg, norm_neg, norm_evaluate_teichPrime, hp, max_eq_left hr.le] using h

private theorem powered_log (r : Radius) :
    Real.log (poweredRadius D w r).val.toReal =
      (Arithmetic.residueChar w.1 : ℝ) * Real.log r.val.toReal := by
  change Real.log ((r.val ^ Arithmetic.residueChar w.1).toReal) = _
  rw [ENNReal.toReal_pow, Real.log_pow]

private theorem log_twisted_recurrence (r : Radius)
    (hr : (poweredRadius D w r).val.toReal < primeNorm D w)
    (x : Carrier D w) (hx : x ≠ 0)
    (he : (Arithmetic.residueChar w.1 : Carrier D w) * frobeniusEquiv D w x =
      primitive D w ^ 2 * x) :
    Real.log (coordinateSeminorm D w (poweredRadius D w r) x) =
      (Arithmetic.residueChar w.1 : ℝ) * Real.log (coordinateSeminorm D w r x) +
      (Arithmetic.residueChar w.1 : ℝ) * Real.log r.val.toReal - 2 * Real.log (primeNorm D w) := by
  have h := congrArg (coordinateSeminorm D w (poweredRadius D w r)) he
  rw [coordinateSeminorm_mul, coordinateSeminorm_mul, coordinateSeminorm_frobenius] at h
  have hp : coordinateSeminorm D w (poweredRadius D w r)
      (Arithmetic.residueChar w.1 : Carrier D w) = (poweredRadius D w r).val.toReal := by
    change ‖evaluate D w _ (Arithmetic.residueChar w.1 : Carrier D w)‖ = _
    simpa only [map_natCast] using
      InitialThetaWittRhoCompletion.inclusion_prime_norm D w (poweredRadius D w r)
  have hξ : coordinateSeminorm D w (poweredRadius D w r) (primitive D w ^ 2) = primeNorm D w ^ 2 := by
    change ‖evaluate D w _ (primitive D w ^ 2)‖ = _
    rw [map_pow, norm_pow]
    exact congrArg (fun a : ℝ => a ^ 2) (primitive_small_radius_norm D w _ hr)
  rw [hp, hξ] at h
  have hl := congrArg Real.log h
  rw [Real.log_mul (radius_toReal_pos _).ne' (pow_pos (coordinate_pos D w r x hx) _).ne',
    Real.log_mul (pow_pos (primeNorm_pos_lt_one D w).1 2).ne'
      (coordinate_pos D w _ x hx).ne', Real.log_pow, Real.log_pow, powered_log D w r] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith

private theorem twisted_quotient_eq_zero (x : Carrier D w)
    (he : (Arithmetic.residueChar w.1 : Carrier D w) * frobeniusEquiv D w x =
      primitive D w ^ 2 * x) : x = 0 := by
  by_contra hx
  let r₀ : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  obtain ⟨n, hn⟩ := ((radiusOrbit_toReal_tendsto_zero D w r₀).eventually
    (gt_mem_nhds (primeNorm_pos_lt_one D w).1)).exists
  let r := radiusOrbit D w r₀ n
  have hle (s : Radius) : (poweredRadius D w s).val.toReal ≤ s.val.toReal := by
    change (s.val ^ Arithmetic.residueChar w.1).toReal ≤ _
    rw [ENNReal.toReal_pow]
    simpa only [pow_one] using pow_le_pow_of_le_one (radius_toReal_pos s).le
      (InitialThetaWittExponentialLinearization.radius_toReal_lt_one s).le
      (Arithmetic.residueChar_prime w.1).pos
  have hsmall : (poweredRadius D w r).val.toReal < primeNorm D w := (hle r).trans_lt hn
  have hsmall₂ : (poweredRadius D w (poweredRadius D w r)).val.toReal < primeNorm D w :=
    (hle _).trans_lt hsmall
  have h₁ := log_twisted_recurrence D w r hsmall x hx he
  have h₂ := log_twisted_recurrence D w (poweredRadius D w r) hsmall₂ x hx he
  rw [powered_log D w r] at h₂
  have hc := InitialThetaWittFrobeniusWeight.log_coordinate_convex D w r x hx
  let p : ℝ := Arithmetic.residueChar w.1
  have hp : 1 < p := by
    change (1 : ℝ) < (Arithmetic.residueChar w.1 : ℝ)
    exact_mod_cast (Arithmetic.residueChar_prime w.1).one_lt
  have ht : Real.log r.val.toReal < 0 := Real.log_neg (radius_toReal_pos r)
    (InitialThetaWittExponentialLinearization.radius_toReal_lt_one r)
  have hbad : 0 ≤ p * (p - 1) * Real.log r.val.toReal := by
    rw [h₂, h₁] at hc
    dsimp [p]
    nlinarith [hc]
  have hneg : p * (p - 1) * Real.log r.val.toReal < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by linarith) (sub_pos.mpr hp)) ht
  exact (not_le_of_gt hneg) hbad

private theorem orbit_sq_dvd (x : Eigen D w) (hd : primitive D w ^ 2 ∣ x.val) (n : ℕ) :
    primitiveOrbit D w n ^ 2 ∣ x.val := by
  induction n with
  | zero => simpa only [primitiveOrbit_zero] using hd
  | succ n ih =>
    have h := map_dvd (frobeniusEquiv D w).toRingHom ih
    have he : frobeniusEquiv D w x.val = (Arithmetic.residueChar w.1 : Carrier D w) * x.val := by
      have hEigen : frobeniusEquiv D w x.val =
          (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x.val := x.property
      simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hEigen
    change frobeniusEquiv D w (primitiveOrbit D w n ^ 2) ∣ frobeniusEquiv D w x.val at h
    rw [map_pow, he, ← primitiveOrbit_succ] at h
    exact (InitialThetaWittEigenKernelFiniteDivision.prime_isUnit D w).dvd_mul_left.mp h

private theorem partial_sq_dvd (x : Eigen D w) (hd : primitive D w ^ 2 ∣ x.val) (N : ℕ) :
    partialProduct D w N ^ 2 ∣ x.val := by
  have hpair : Pairwise (fun m n => IsCoprime (primitiveOrbit D w m ^ 2) (primitiveOrbit D w n ^ 2)) :=
    fun m n hmn => ((primitiveOrbit_pairwise_isCoprime D w) hmn).pow
  have hprod : finiteProduct D w (Finset.range N) ^ 2 ∣ x.val := by
    rw [finiteProduct, ← Finset.prod_pow]
    exact Finset.prod_dvd_of_coprime (hpair.set_pairwise _) (fun n _ => orbit_sq_dvd D w x hd n)
  rw [partial_eq_scaled_finiteProduct, mul_pow]
  exact (((scaleUnit D w).isUnit.pow N).pow 2).mul_left_dvd.mpr hprod

private theorem exists_product_sq_quotient (x : Eigen D w) (hd : primitive D w ^ 2 ∣ x.val) :
    ∃ y : Carrier D w, product D w ^ 2 * y = x.val := by
  let q : ℕ → Carrier D w := fun N => Classical.choose (partial_sq_dvd D w x hd N)
  have hq (N : ℕ) : partialProduct D w N ^ 2 * q N = x.val :=
    (Classical.choose_spec (partial_sq_dvd D w x hd N)).symm
  have hcρ (r : Radius) : CauchySeq (fun N => evaluate D w r (q N)) := by
    apply MultiplicativeNormDivisionLimit.cauchySeq_quotient
      (fun N => evaluate D w r (partialProduct D w N ^ 2)) _ (evaluate D w r x.val)
        (evaluate D w r (product D w ^ 2))
    · intro N
      apply norm_ne_zero_iff.mp
      rw [map_pow, norm_pow]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (evaluate_partial_ne_zero D w r N))
    · apply norm_ne_zero_iff.mp
      rw [map_pow, norm_pow, evaluate_product]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (completedProduct_ne_zero D w r))
    · exact ((evaluate_continuous D w r).tendsto (product D w ^ 2)).comp ((partial_tendsto D w).pow 2)
    · intro N
      rw [← map_mul, hq]
  have hc : CauchySeq q := by
    apply isUniformEmbedding_subtype_val.isUniformInducing.cauchy_map_iff.mp
    rw [Filter.map_map]
    apply (cauchy_pi_iff' (l := Filter.map (fun N => fun r => evaluate D w r (q N)) Filter.atTop)).mpr
    intro r
    rw [Filter.map_map]
    exact hcρ r
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  have h := ((partial_tendsto D w).pow 2).mul hy
  simp only [hq] at h
  exact ⟨y, tendsto_nhds_unique h tendsto_const_nhds⟩

theorem primitive_sq_dvd_eigen_iff (x : Eigen D w) : primitive D w ^ 2 ∣ x.val ↔ x = 0 := by
  constructor
  · intro hd
    obtain ⟨y, hy⟩ := exists_product_sq_quotient D w x hd
    have hEigen : frobeniusEquiv D w x.val = (Arithmetic.residueChar w.1 : Carrier D w) * x.val := by
      have h : frobeniusEquiv D w x.val =
          (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x.val := x.property
      simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using h
    have he := congrArg (frobeniusEquiv D w) hy
    rw [map_mul, map_pow, hEigen, ← hy] at he
    have hP := InitialThetaWittNormalizedOrbitProductFiniteFrobenius.product_frobenius_mul_factor_zero D w
    have hcancel := (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w
      (frobeniusEquiv D w (product D w))
      (InitialThetaWittEigenKernelTwistedComparison.frobenius_product_ne_zero D w)).injective
    have htw : frobeniusEquiv D w y =
        (Arithmetic.residueChar w.1 : Carrier D w) * factor D w 0 ^ 2 * y := by
      apply hcancel
      apply hcancel
      change frobeniusEquiv D w (product D w) * (frobeniusEquiv D w (product D w) *
        frobeniusEquiv D w y) = frobeniusEquiv D w (product D w) *
          (frobeniusEquiv D w (product D w) *
            ((Arithmetic.residueChar w.1 : Carrier D w) * factor D w 0 ^ 2 * y))
      calc
        _ = frobeniusEquiv D w (product D w) ^ 2 * frobeniusEquiv D w y := by ring
        _ = (Arithmetic.residueChar w.1 : Carrier D w) * (product D w ^ 2 * y) := he
        _ = _ := by
          conv_lhs => rw [← hP]
          ring
    have hzero : y = 0 := by
      apply twisted_quotient_eq_zero D w y
      rw [htw]
      calc
        _ = ((Arithmetic.residueChar w.1 : Carrier D w) * factor D w 0) ^ 2 * y := by ring
        _ = _ := by rw [InitialThetaWittTwistedTatePeriod.prime_mul_factor_zero, neg_sq]
    apply Subtype.ext
    change x.val = 0
    rw [← hy, hzero, mul_zero]
  · rintro rfl
    exact dvd_zero _

theorem quotientEvaluation_injective :
    Function.Injective (InitialThetaWittEigenKernelFirstOrder.quotientEvaluation D w) := by
  intro x y hxy
  have hz : InitialThetaWittEigenKernelFirstOrder.quotientEvaluation D w (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hd := (InitialThetaWittEigenKernelFirstOrder.primitive_sq_dvd_iff_quotientEvaluation_zero
    D w (x - y)).mpr hz
  let e : Eigen D w := ⟨(x - y).val, (x - y).property.1⟩
  have he : e = 0 := (primitive_sq_dvd_eigen_iff D w e).mp hd
  have hval := congrArg (fun z : Eigen D w => z.val) he
  change (x - y).val = 0 at hval
  have hzero : x - y = 0 := Subtype.ext hval
  exact sub_eq_zero.mp hzero

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelSimpleZero
