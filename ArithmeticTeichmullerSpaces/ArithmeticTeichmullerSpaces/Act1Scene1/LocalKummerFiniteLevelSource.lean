import ArithmeticTeichmullerSpaces.Act1Scene1.GaloisLocallyConstantHilbert90
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerH1Equivalence

/-!
source-id: JT-SCENE1-INTEGRAL-KUMMER-FINITE-LEVEL-SOURCE
source: finite-level values of the original integral Tate cocycle, locally
constant Galois Hilbert 90 and actual fixed-field descent; Joshi III 3190--3236.
fidelity: at every level n, constructs a nonzero base-field element and a
p^n-th root whose Galois ratio is the given integral cocycle at that level.
These are genuine field elements, not a renamed cohomology carrier. Coherent
base representatives and a full integral Kummer comparison remain separate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [IsGalois K Ω] [Algebra.IsIntegral K Ω]
variable (p : ℕ) [Fact p.Prime]

theorem finiteLevel_coboundary (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) :
    ∃ b : Ωˣ, ∀ σ : Ω ≃ₐ[K] Ω, σ (b : Ω) / (b : Ω) = ((f.1 σ).1 n : Ω) := by
  have hloc : IsLocallyConstant (fun σ : Ω ≃ₐ[K] Ω => (f.1 σ).1 n) :=
    (continuous_tate_iff_level_locallyConstant _).mp f.1.continuous n
  have hf : groupCohomology.IsMulCocycle₁ (fun σ : Ω ≃ₐ[K] Ω => (f.1 σ).1 n) := by
    intro σ τ
    exact congrArg (fun x : cyclotomicTateGroup p Ω => x.1 n) (f.2 σ τ)
  obtain ⟨b, hb⟩ := GaloisCocycle.locallyConstant_hilbert90 _ hloc hf
  refine ⟨b, fun σ => ?_⟩
  have h := congrArg (fun x : Ωˣ => (x : Ω)) (hb σ)
  have hs : ((σ • b : Ωˣ) : Ω) = σ (b : Ω) := rfl
  simpa only [Units.val_div_eq_div_val, hs] using h

theorem finiteLevel_field_source (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) :
    ∃ (a : K) (b : Ωˣ), a ≠ 0 ∧ (b : Ω) ^ (p ^ n) = algebraMap K Ω a ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ (b : Ω) / (b : Ω) = ((f.1 σ).1 n : Ω) := by
  obtain ⟨b, hb⟩ := finiteLevel_coboundary p f n
  have hfixed (σ : Ω ≃ₐ[K] Ω) : σ ((b : Ω) ^ (p ^ n)) = (b : Ω) ^ (p ^ n) := by
    have h := congrArg (fun x : Ω => x ^ (p ^ n)) (hb σ)
    have hroot := congrArg (fun x : Ωˣ => (x : Ω)) ((f.1 σ).2.1 n)
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hroot
    rw [div_pow, hroot] at h
    rw [map_pow]
    exact (div_eq_one_iff_eq (pow_ne_zero _ b.ne_zero)).mp h
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr hfixed
  refine ⟨a, b, ?_, ha.symm, hb⟩
  intro hzero
  rw [hzero, map_zero] at ha
  exact pow_ne_zero _ b.ne_zero ha.symm

theorem successive_roots_ratio_in_base
    (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) (b c : Ωˣ)
    (hb : ∀ σ : Ω ≃ₐ[K] Ω, σ (b : Ω) / (b : Ω) = ((f.1 σ).1 n : Ω))
    (hc : ∀ σ : Ω ≃ₐ[K] Ω, σ (c : Ω) / (c : Ω) = ((f.1 σ).1 (n + 1) : Ω)) :
    ∃ d : K, d ≠ 0 ∧ algebraMap K Ω d = (c : Ω) ^ p / (b : Ω) := by
  have hfixed (σ : Ω ≃ₐ[K] Ω) :
      σ ((c : Ω) ^ p / (b : Ω)) = (c : Ω) ^ p / (b : Ω) := by
    have ht := congrArg (fun x : Ωˣ => (x : Ω)) ((f.1 σ).2.2 n)
    have he : σ (c : Ω) ^ p / (c : Ω) ^ p = σ (b : Ω) / (b : Ω) := by
      rw [← div_pow, hc, hb]
      exact ht
    have hs : σ (b : Ω) ≠ 0 := by simpa only [map_zero] using σ.injective.ne b.ne_zero
    rw [map_div₀, map_pow]
    apply (div_eq_div_iff hs b.ne_zero).mpr
    have hh := (div_eq_div_iff (pow_ne_zero _ c.ne_zero) b.ne_zero).mp he
    simpa only [mul_comm] using hh
  obtain ⟨d, hd⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr hfixed
  refine ⟨d, ?_, hd⟩
  intro hz
  rw [hz, map_zero] at hd
  exact div_ne_zero (pow_ne_zero _ c.ne_zero) b.ne_zero hd.symm

/-- The actual base representatives are compatible modulo p^n-th powers.
The correction d is derived from the adjacent roots in the original extension. -/
theorem finiteLevel_sources_compatible (f : continuousCocycles (K := K) (Ω := Ω) p) :
    ∃ (a : ℕ → K) (b : ℕ → Ωˣ),
      (∀ n, a n ≠ 0 ∧ (b n : Ω) ^ (p ^ n) = algebraMap K Ω (a n) ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ (b n : Ω) / (b n : Ω) = ((f.1 σ).1 n : Ω)) ∧
      ∀ n, ∃ d : K, d ≠ 0 ∧ a (n + 1) = d ^ (p ^ n) * a n := by
  choose a b ha hab hb using finiteLevel_field_source p f
  refine ⟨a, b, fun n => ⟨ha n, hab n, hb n⟩, fun n => ?_⟩
  obtain ⟨d, hd0, hd⟩ := successive_roots_ratio_in_base p f n (b n) (b (n + 1))
    (hb n) (hb (n + 1))
  refine ⟨d, hd0, (algebraMap K Ω).injective ?_⟩
  rw [map_mul, map_pow, hd, div_pow, ← hab n, ← hab (n + 1),
    ← pow_mul, ← pow_succ']
  exact (div_mul_cancel₀ _ (pow_ne_zero _ (b n).ne_zero)).symm

theorem every_integralClass_finiteLevel_source
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)) :
    ∃ f : continuousCocycles (K := K) (Ω := Ω) p,
      padicClassOfCocycle p f = x ∧ ∀ n : ℕ,
        ∃ (a : K) (b : Ωˣ), a ≠ 0 ∧ (b : Ω) ^ (p ^ n) = algebraMap K Ω a ∧
          ∀ σ : Ω ≃ₐ[K] Ω, σ (b : Ω) / (b : Ω) = ((f.1 σ).1 n : Ω) := by
  obtain ⟨c, hc⟩ := toPadicH1_surjective p x
  induction c using Quotient.inductionOn with
  | h f => exact ⟨f, hc, finiteLevel_field_source p f⟩

end
end JoshiTeich.Act1Scene1.LocalKummer
