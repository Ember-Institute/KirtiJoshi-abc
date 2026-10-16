import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerFiniteLevelDetection

/-!
source-id: JT-SCENE1-INTEGRAL-KUMMER-FINITE-SOURCE-ZERO
source: actual finite-level Hilbert 90 field representatives, fixed-field
descent and compact finite-level detection; Joshi III 3190--3236.
fidelity: for the actual finite-level field sources of an integral cocycle,
the original H1 class is zero iff every source is a p^n-th power in the base.
The final theorem constructs the sources for each standard integral H1 class.
No infinite compatible choice of base roots is supplied by a caller.
boundary: Scene1/Derived; inverse-limit surjectivity and H1e/BK remain separate.
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [IsGalois K Ω] [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

theorem padicClass_eq_zero_iff_source_powers
    (f : continuousCocycles (K := K) (Ω := Ω) p) (a : ℕ → K) (b : ℕ → Ωˣ)
    (ha : ∀ n, a n ≠ 0)
    (hab : ∀ n, (b n : Ω) ^ (p ^ n) = algebraMap K Ω (a n))
    (hb : ∀ n (σ : Ω ≃ₐ[K] Ω), σ (b n : Ω) / (b n : Ω) = ((f.1 σ).1 n : Ω)) :
    padicClassOfCocycle p f = 0 ↔ ∀ n : ℕ, ∃ r : K, r ^ (p ^ n) = a n := by
  constructor
  · intro hf n
    obtain ⟨z, hz, hzf⟩ := (padicClass_eq_zero_iff_all_finiteLevels p f).mp hf n
    have hfixed (σ : Ω ≃ₐ[K] Ω) : σ ((b n : Ω) / (z : Ω)) = (b n : Ω) / (z : Ω) := by
      have he : σ (b n : Ω) / (b n : Ω) = σ (z : Ω) / (z : Ω) := by
        rw [hb]
        have h := congrArg (fun u : Ωˣ => (u : Ω)) (hzf σ)
        have hs : ((σ • z : Ωˣ) : Ω) = σ (z : Ω) := rfl
        simpa only [Units.val_div_eq_div_val, hs] using h
      have hs0 : σ (z : Ω) ≠ 0 := by simpa only [map_zero] using σ.injective.ne z.ne_zero
      rw [map_div₀]
      apply (div_eq_div_iff hs0 z.ne_zero).mpr
      simpa only [mul_comm] using (div_eq_div_iff (b n).ne_zero z.ne_zero).mp he
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr hfixed
    refine ⟨r, (algebraMap K Ω).injective ?_⟩
    have hz' := congrArg (fun u : Ωˣ => (u : Ω)) hz
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hz'
    rw [map_pow, hr, div_pow, hz', div_one, hab]
  · intro hroot
    apply (padicClass_eq_zero_iff_all_finiteLevels p f).mpr
    intro n
    obtain ⟨r, hr⟩ := hroot n
    have hr0 : r ≠ 0 := by
      intro hz
      rw [hz, zero_pow (pow_pos (Fact.out : p.Prime).pos n).ne'] at hr
      exact ha n hr.symm
    let R : Ωˣ := Units.mk0 (algebraMap K Ω r) ((map_ne_zero (algebraMap K Ω)).mpr hr0)
    let z : Ωˣ := b n / R
    have hzval : (z : Ω) = (b n : Ω) / algebraMap K Ω r := by
      dsimp only [z]
      rw [Units.val_div_eq_div_val]
      rfl
    have hR (σ : Ω ≃ₐ[K] Ω) : σ • R = R := by
      apply Units.ext
      exact σ.commutes r
    refine ⟨z, ?_, fun σ => ?_⟩
    · apply Units.ext
      change ((z ^ (p ^ n) : Ωˣ) : Ω) = 1
      rw [Units.val_pow_eq_pow_val, hzval]
      rw [div_pow, ← map_pow, hr, hab, div_self]
      exact (map_ne_zero (algebraMap K Ω)).mpr (ha n)
    · have hh := hb n σ
      have hbf : (f.1 σ).1 n = σ • b n / b n := by
        apply Units.ext
        rw [Units.val_div_eq_div_val]
        exact hh.symm
      rw [hbf]
      change σ • b n / b n = σ • (b n / R) / (b n / R)
      rw [smul_div', hR, div_div_div_cancel_right]

theorem every_integralClass_has_source_zero_criterion
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)) :
    ∃ (a : ℕ → K) (b : ℕ → Ωˣ),
      (∀ n, a n ≠ 0 ∧ (b n : Ω) ^ (p ^ n) = algebraMap K Ω (a n)) ∧
      (x = 0 ↔ ∀ n : ℕ, ∃ r : K, r ^ (p ^ n) = a n) ∧
      ∀ n, ∃ d : K, d ≠ 0 ∧ a (n + 1) = d ^ (p ^ n) * a n := by
  obtain ⟨c, hc⟩ := toPadicH1_surjective p x
  induction c using Quotient.inductionOn with
  | h f =>
    obtain ⟨a, b, hs, hcompat⟩ := finiteLevel_sources_compatible p f
    refine ⟨a, b, fun n => ⟨(hs n).1, (hs n).2.1⟩, ?_, hcompat⟩
    rw [← hc]
    exact padicClass_eq_zero_iff_source_powers p f a b
      (fun n => (hs n).1) (fun n => (hs n).2.1) (fun n => (hs n).2.2)

end
end JoshiTeich.Act1Scene1.LocalKummer
