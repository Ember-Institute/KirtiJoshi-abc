import ArithmeticTeichmullerSpaces.Act1Scene1.PadicCompactDenominator
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientKernel
import Mathlib.FieldTheory.Galois.Profinite

/-!
source-id: JT-SCENE1-CONTINUOUS-H1-INTEGRAL-DENOMINATOR
source: compact Krull Galois group, original Tate coordinates and continuous
H1 representatives; Joshi III 3214--3236.
fidelity: every rational continuous H1 class becomes an image of the original
integral coefficient map after multiplication by a p power. The integral
cocycle is constructed continuously from a uniformly bounded representative.
This does not assert that integral cocycles come from field elements, nor
identify H1e/BK or prove multiplicative Kummer surjectivity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [IsGalois K Ω] [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]
local notation "G" => Ω ≃ₐ[K] Ω
local notation "HI" => continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)
local notation "HQ" => continuousCohomology 1 (topRep (K := K) (Ω := Ω) p)

theorem exists_scaled_integral_cocycle
    (f : C(G, topRep (K := K) (Ω := Ω) p))
    (hf : ∀ σ τ, f (σ * τ) = (topRep p).ρ σ (f τ) + f σ) :
    ∃ (n : ℕ) (g : continuousCocycles (K := K) (Ω := Ω) p),
      cocycle p g = (p : ℚ_[p]) ^ n • f := by
  let F : C(G, ℚ_[p]) := ⟨fun σ => (f σ).down, continuous_uliftDown.comp f.continuous⟩
  obtain ⟨n, hn⟩ := PadicCompact.exists_uniform_denominator p F
  let b := PadicCompact.integralLift p F n hn
  let a : C(G, Additive (cyclotomicTateGroup p Ω)) :=
    ⟨fun σ => TateBasis.equiv (p := p) (Ω := Ω) (b σ),
      (TateBasis.equiv (p := p) (Ω := Ω)).continuous.comp b.continuous⟩
  have ha (σ : G) : coefficientMap p (a σ) = (p : ℚ_[p]) ^ n * (f σ).down :=
    coefficientMap_basis p (b σ)
  have halaw (σ τ : G) : a (σ * τ) = padicTateRepresentation p σ (a τ) + a σ := by
    apply coefficientMap_injective p
    rw [map_add, coefficientMap_equivariant, ha, ha, ha]
    have h := congrArg ULift.down (hf σ τ)
    change (f (σ * τ)).down = representation p σ (f τ).down + (f σ).down at h
    rw [h]
    change (p : ℚ_[p]) ^ n * ((f τ).down * (Cyclotomic.coefficient p σ : ℚ_[p]) + (f σ).down) =
      ((p : ℚ_[p]) ^ n * (f τ).down) * (Cyclotomic.coefficient p σ : ℚ_[p]) +
        (p : ℚ_[p]) ^ n * (f σ).down
    ring
  let g : continuousCocycles (K := K) (Ω := Ω) p :=
    ⟨⟨fun σ => (a σ).toMul, continuous_toMul.comp a.continuous⟩,
      fun σ τ => congrArg Additive.toMul (halaw σ τ)⟩
  refine ⟨n, g, ?_⟩
  ext σ
  apply ULift.ext
  exact ha σ

theorem exists_prime_power_integralLift (x : HQ) :
    ∃ (n : ℕ) (y : HI), standardMap p y = (p : ℚ_[p]) ^ n • x := by
  obtain ⟨f, hf, rfl⟩ := ContinuousH1Recognition.classOf_surjective (topRep p) x
  obtain ⟨n, g, hg⟩ := exists_scaled_integral_cocycle p f hf
  refine ⟨n, padicClassOfCocycle p g, ?_⟩
  rw [standardMap_classOfCocycle, classOfCocycle]
  change ContinuousH1Homogeneous.classOf (topRep p) (cocycle p g) _ = _
  simpa only [hg] using ContinuousH1Homogeneous.classOf_smul (topRep p) ((p : ℚ_[p]) ^ n) f hf

theorem exists_divided_integralLift (x : HQ) :
    ∃ (n : ℕ) (y : HI), x = ((p : ℚ_[p]) ^ n)⁻¹ • standardMap p y := by
  obtain ⟨n, y, hy⟩ := exists_prime_power_integralLift p x
  refine ⟨n, y, ?_⟩
  rw [hy, smul_smul, inv_mul_cancel₀ (pow_ne_zero n
    (show (p : ℚ_[p]) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)), one_smul]

/-- The actual integral coefficient image spans all rational continuous H1. -/
theorem span_integralCoefficientImage_eq_top :
    Submodule.span ℚ_[p] (Set.range (standardMap (K := K) (Ω := Ω) p)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, y, hx⟩ := exists_divided_integralLift p x
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)

end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
