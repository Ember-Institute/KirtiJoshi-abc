import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientChange
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTowerPowers
import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Recognition

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-RATIONAL-DENOMINATOR
source: integral/rational Kummer comparison, Joshi III (3214--3236).
fidelity: any rational coboundary can be multiplied by a p power so that
its witness belongs to the actual integral Tate lattice. Thus zero of a
rational root-tower class forces zero of the integral class of a p-power
of the original element. It does not assert H1 coefficient injectivity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
open Filter Topology
universe u v
noncomputable section
variable (p : ℕ) [Fact p.Prime]

theorem exists_integral_p_power_mul (q : ℚ_[p]) :
    ∃ (n : ℕ) (z : ℤ_[p]), (z : ℚ_[p]) = (p : ℚ_[p]) ^ n * q := by
  have ht : Tendsto (fun n : ℕ => ‖(p : ℚ_[p])‖ ^ n * ‖q‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (Padic.norm_p_lt_one (p := p))).mul_const ‖q‖
  obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 1 zero_lt_one).exists
  refine ⟨n, Padic.lift ((p : ℚ_[p]) ^ n * q) ?_, rfl⟩
  simpa only [norm_mul, norm_pow] using hn.le

variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]

theorem exists_scaled_integral_coboundary
    (f : continuousCocycles (K := K) (Ω := Ω) p) (hz : classOfCocycle p f = 0) :
    ∃ (n : ℕ) (t : Additive (cyclotomicTateGroup p Ω)), ∀ σ : Ω ≃ₐ[K] Ω,
      (p ^ n : ℕ) • Additive.ofMul (f.1 σ) = padicTateRepresentation p σ t - t := by
  obtain ⟨q, hq⟩ := (ContinuousH1Recognition.classOf_eq_zero_iff (topRep p)
    (cocycle p f) (cocycle_law p f)).mp hz
  obtain ⟨n, z, hz⟩ := exists_integral_p_power_mul p q.down
  let t := TateBasis.equiv (p := p) (Ω := Ω) z
  have ht : coefficientMap p t = (p : ℚ_[p]) ^ n * q.down :=
    (coefficientMap_basis p z).trans hz
  refine ⟨n, t, fun σ => ?_⟩
  apply coefficientMap_injective p
  have hs := congrArg ULift.down (hq σ)
  change coefficientMap p (Additive.ofMul (f.1 σ)) = representation p σ q.down - q.down at hs
  rw [← padic_smul_natCast, coefficientMap_smul, map_sub, coefficientMap_equivariant,
    PadicInt.coe_natCast, Nat.cast_pow, ht]
  rw [hs]
  change (p : ℚ_[p]) ^ n * (q.down * (Cyclotomic.coefficient p σ : ℚ_[p]) - q.down) =
    ((p : ℚ_[p]) ^ n * q.down) * (Cyclotomic.coefficient p σ : ℚ_[p]) - (p : ℚ_[p]) ^ n * q.down
  ring

theorem integral_powClass_eq_zero_of_rational_eq_zero {a : K}
    (R : RootTower (Ω := Ω) p a) (ha : a ≠ 0)
    (h : classOfCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos ha) = 0) :
    ∃ n : ℕ, ∃ hpow : a ^ (p ^ n) ≠ 0,
      padicClassOfCocycle p
        ((R.pow (p ^ n)).continuousCocycleValue (Fact.out : p.Prime).pos
          (a := a ^ (p ^ n)) hpow) = 0 := by
  obtain ⟨n, t, ht⟩ := exists_scaled_integral_coboundary p _ h
  have hpow : a ^ (p ^ n) ≠ 0 := pow_ne_zero (p ^ n) ha
  let Rp : RootTower (K := K) (Ω := Ω) p (a ^ (p ^ n)) := R.pow (p ^ n)
  let fp : continuousCocycles (K := K) (Ω := Ω) p :=
    ⟨RootTower.continuousCocycle (K := K) (Ω := Ω) (a := a ^ (p ^ n))
        Rp (Fact.out : p.Prime).pos hpow,
      RootTower.continuousCocycle_isMulCocycle (K := K) (Ω := Ω)
        (a := a ^ (p ^ n)) Rp (Fact.out : p.Prime).pos hpow⟩
  have hz : LocalKummer.padicClassOfCocycle (K := K) (Ω := Ω) p fp = 0 := by
    apply (padicClassOfCocycle_eq_zero_iff p fp).mpr
    refine ⟨t.toMul, fun σ => ?_⟩
    change Rp.kummerCocycle (a := a ^ (p ^ n)) (Fact.out : p.Prime).pos hpow σ = _
    rw [R.pow_cocycle (p ^ n) (Fact.out : p.Prime).pos ha σ]
    exact congrArg Additive.toMul (ht σ)
  exact ⟨n, hpow, by convert hz using 1 <;> rfl⟩

end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
