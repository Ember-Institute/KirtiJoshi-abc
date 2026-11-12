import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRationalDenominator
import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Scalar

/-!
source-id: JT-SCENE1-KUMMER-COEFFICIENT-KERNEL
source: the original integral/rational coefficient map and denominator
clearing of rational coboundaries, Joshi III 3214--3236.
fidelity: for every standard integral H1 class, its rational image is zero
iff a p power kills the class. Equal rational images have p-power-torsion
difference. No injectivity of the original coefficient map is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]
local notation "HI" => continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)
local notation "HQ" => continuousCohomology 1 (topRep (K := K) (Ω := Ω) p)

theorem padicClass_smul_eq_zero_of_coboundary
    (f : continuousCocycles (K := K) (Ω := Ω) p) (r : ℤ_[p])
    (t : Additive (cyclotomicTateGroup p Ω))
    (ht : ∀ σ : Ω ≃ₐ[K] Ω, r • Additive.ofMul (f.1 σ) = padicTateRepresentation p σ t - t) :
    r • padicClassOfCocycle p f = 0 := by
  rw [padicClassOfCocycle, ← ContinuousH1Homogeneous.classOf_smul]
  apply (ContinuousH1Recognition.classOf_eq_zero_iff _ _ _).mpr
  exact ⟨t, ht⟩

theorem standardMap_eq_zero_iff_prime_power_torsion (x : HI) :
    standardMap p x = 0 ↔ ∃ n : ℕ, (p ^ n) • x = 0 := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := toPadicH1_surjective p x
    induction c using Quotient.inductionOn with
    | h f =>
      change standardMap p (padicClassOfCocycle p f) = 0 at hx
      rw [standardMap_classOfCocycle] at hx
      obtain ⟨n, t, ht⟩ := exists_scaled_integral_coboundary p f hx
      refine ⟨n, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul ℤ_[p]]
      apply padicClass_smul_eq_zero_of_coboundary p f (p ^ n : ℕ) t
      intro σ
      rw [Nat.cast_smul_eq_nsmul]
      exact ht σ
  · rintro ⟨n, hn⟩
    apply standardMap_eq_zero_of_torsion p (p ^ n : ℤ_[p])
      (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) x
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hn

theorem standardMap_eq_iff_prime_power_difference (x y : HI) :
    standardMap p x = standardMap p y ↔ ∃ n : ℕ, (p ^ n) • (x - y) = 0 := by
  rw [← sub_eq_zero, ← map_sub, standardMap_eq_zero_iff_prime_power_torsion]

/-- Divided rational classes lift exactly when the integral class is divisible modulo torsion. -/
theorem standardMap_eq_divided_iff (r : ℤ_[p]) (hr : r ≠ 0) (x y : HI) :
    standardMap p x = (r : ℚ_[p])⁻¹ • standardMap p y ↔
      ∃ n : ℕ, (p ^ n) • (r • x - y) = 0 := by
  rw [← standardMap_eq_iff_prime_power_difference]
  have hrQ : (r : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hr
  constructor
  · intro h
    rw [map_smulₛₗ]
    change (r : ℚ_[p]) • standardMap p x = standardMap p y
    rw [h, smul_smul, mul_inv_cancel₀ hrQ, one_smul]
  · intro h
    rw [map_smulₛₗ] at h
    change (r : ℚ_[p]) • standardMap p x = standardMap p y at h
    have he := congrArg (fun z : HQ => (r : ℚ_[p])⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ hrQ, one_smul] using he

/-- This is the actual kernel submodule of the original semilinear coefficient map. -/
def coefficientTorsion : Submodule ℤ_[p] HI := (standardMap (K := K) (Ω := Ω) p).ker

theorem mem_coefficientTorsion_iff (x : HI) :
    x ∈ coefficientTorsion p ↔ ∃ n : ℕ, (p ^ n) • x = 0 :=
  standardMap_eq_zero_iff_prime_power_torsion p x

local instance rationalH1IntegralModule : Module ℤ_[p] HQ :=
  Module.compHom HQ (PadicInt.Coe.ringHom (p := p))

/-- Scalar restriction uses the original rational H1 action. -/
def coefficientIntegralLinear : HI →ₗ[ℤ_[p]] HQ where
  toFun := standardMap p
  map_add' := map_add (standardMap p)
  map_smul' := (standardMap p).map_smulₛₗ

/-- The original coefficient map descends to an injective map after removing its proved torsion. -/
def torsionFreeCoefficient : (HI ⧸ coefficientTorsion p) →ₗ[ℤ_[p]] HQ :=
  (coefficientTorsion p).liftQ (coefficientIntegralLinear p) (by
    intro x hx
    exact hx)

theorem torsionFreeCoefficient_mk (x : HI) :
    torsionFreeCoefficient p ((coefficientTorsion p).mkQ x) = standardMap p x := rfl

theorem torsionFreeCoefficient_injective :
    Function.Injective (torsionFreeCoefficient (K := K) (Ω := Ω) p) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨x, rfl⟩ := (coefficientTorsion p).mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero (coefficientTorsion p)).mpr
  exact hx

end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
