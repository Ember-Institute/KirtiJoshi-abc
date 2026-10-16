import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCompatibleSourceTower
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerFiniteSourceZeroCriterion

/-!
source-id: JT-SCENE1-COMPATIBLE-KUMMER-SOURCE-REALIZATION
source: compatible base power-class representatives, actual corrected roots,
finite-level detection and standard integral continuous H1; Joshi III 3190--3236.
fidelity: realizes every compatible nonzero base representative family by a
continuous integral Tate cocycle. Equal source representatives give the same
H1 class. Reconstructing any original cocycle's finite sources recovers its
original standard class. No inverse-limit quotient is renamed as H1.
boundary: Scene1/Derived; local-field realization by a single field element
or its Q_p span and H1e/BK comparison remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

/-- Finite-level source equality suffices, without compatible root choices. -/
theorem padicClass_eq_of_same_sources
    (f g : continuousCocycles (K := K) (Ω := Ω) p)
    (a : ℕ → K) (b c : ℕ → Ωˣ)
    (hb : ∀ n, (b n : Ω) ^ (p ^ n) = algebraMap K Ω (a n))
    (hc : ∀ n, (c n : Ω) ^ (p ^ n) = algebraMap K Ω (a n))
    (hbf : ∀ n (σ : Ω ≃ₐ[K] Ω), σ (b n : Ω) / (b n : Ω) = ((f.1 σ).1 n : Ω))
    (hcg : ∀ n (σ : Ω ≃ₐ[K] Ω), σ (c n : Ω) / (c n : Ω) = ((g.1 σ).1 n : Ω)) :
    padicClassOfCocycle p f = padicClassOfCocycle p g := by
  let h : continuousCocycles (K := K) (Ω := Ω) p :=
    ⟨g.1 / f.1, by
      intro σ τ
      change g.1 (σ * τ) / f.1 (σ * τ) = σ • (g.1 τ / f.1 τ) * (g.1 σ / f.1 σ)
      rw [g.2 σ τ, f.2 σ τ, smul_div', mul_div_mul_comm]⟩
  have hz : padicClassOfCocycle p h = 0 := by
    apply (padicClass_eq_zero_iff_all_finiteLevels p h).mpr
    intro n
    let z : Ωˣ := c n / b n
    refine ⟨z, ?_, fun σ => ?_⟩
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      have hzval : (z : Ω) = (c n : Ω) / (b n : Ω) := Units.val_div_eq_div_val _ _
      have hm : algebraMap K Ω (a n) ≠ 0 := by
        rw [← hb n]
        exact pow_ne_zero _ (b n).ne_zero
      rw [hzval, div_pow, hc n, hb n, div_self hm, Units.val_one]
    · change (g.1 σ).1 n / (f.1 σ).1 n = σ • z / z
      apply Units.ext
      rw [Units.val_div_eq_div_val, ← hbf n σ, ← hcg n σ, Units.val_div_eq_div_val]
      have hzval : (z : Ω) = (c n : Ω) / (b n : Ω) := Units.val_div_eq_div_val _ _
      have hs : ((σ • z : Ωˣ) : Ω) = σ (z : Ω) := rfl
      rw [hs, hzval, map_div₀]
      have hsb : σ (b n : Ω) ≠ 0 := by simpa only [map_zero] using σ.injective.ne (b n).ne_zero
      have hsc : σ (c n : Ω) ≠ 0 := by simpa only [map_zero] using σ.injective.ne (c n).ne_zero
      field_simp [(b n).ne_zero, (c n).ne_zero, hsb, hsc]
      <;> ring
  obtain ⟨t, ht⟩ := (padicClassOfCocycle_eq_zero_iff p h).mp hz
  apply (padicClassOfCocycle_eq_iff p f g).mpr
  exact ⟨t, fun σ => (ht σ).symm⟩

variable (a : ℕ → K) (ha : ∀ n, a n ≠ 0)
variable (hstep : ∀ n, ∃ d : K, a (n + 1) = d ^ (p ^ n) * a n)

def compatibleSourceCocycle : continuousCocycles (K := K) (Ω := Ω) p :=
  CompatibleSourceTower.continuousCocycleValue
    (CompatibleSourceTower.ofCompatible (Ω := Ω) (Fact.out : p.Prime).pos hstep) ha

theorem compatibleSourceCocycle_field_sources :
    ∃ b : ℕ → Ωˣ, ∀ n,
      (b n : Ω) ^ (p ^ n) = algebraMap K Ω (a n) ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ (b n : Ω) / (b n : Ω) =
          (((compatibleSourceCocycle p a ha hstep).1 σ).1 n : Ω) := by
  let R := CompatibleSourceTower.ofCompatible (Ω := Ω) (Fact.out : p.Prime).pos hstep
  refine ⟨fun n => Units.mk0 (R.root n) (R.root_ne_zero ha n), fun n => ?_⟩
  exact ⟨R.root_pow_eq n, fun _ => rfl⟩

def compatibleSourceClass :
    continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p) :=
  padicClassOfCocycle p (compatibleSourceCocycle p a ha hstep)

theorem compatibleSourceClass_eq_original
    (f : continuousCocycles (K := K) (Ω := Ω) p) (b : ℕ → Ωˣ)
    (hb : ∀ n, (b n : Ω) ^ (p ^ n) = algebraMap K Ω (a n))
    (hbf : ∀ n (σ : Ω ≃ₐ[K] Ω), σ (b n : Ω) / (b n : Ω) = ((f.1 σ).1 n : Ω)) :
    compatibleSourceClass p a ha hstep = padicClassOfCocycle p f := by
  obtain ⟨c, hc⟩ := compatibleSourceCocycle_field_sources (Ω := Ω) p a ha hstep
  exact padicClass_eq_of_same_sources p _ f a c b
    (fun n => (hc n).1) hb (fun n => (hc n).2) hbf

variable [IsGalois K Ω]

theorem compatibleSourceClass_eq_zero_iff :
    compatibleSourceClass (Ω := Ω) p a ha hstep = 0 ↔
      ∀ n : ℕ, ∃ r : K, r ^ (p ^ n) = a n := by
  obtain ⟨b, hb⟩ := compatibleSourceCocycle_field_sources (Ω := Ω) p a ha hstep
  exact padicClass_eq_zero_iff_source_powers p _ a b ha
    (fun n => (hb n).1) (fun n => (hb n).2)

theorem every_integralClass_from_compatible_sources
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)) :
    ∃ (a : ℕ → K) (ha : ∀ n, a n ≠ 0)
      (hstep : ∀ n, ∃ d : K, a (n + 1) = d ^ (p ^ n) * a n),
        compatibleSourceClass (Ω := Ω) p a ha hstep = x := by
  obtain ⟨q, hq⟩ := toPadicH1_surjective p x
  induction q using Quotient.inductionOn with
  | h f =>
    obtain ⟨a, b, hs, hcompat⟩ := finiteLevel_sources_compatible p f
    let ha : ∀ n, a n ≠ 0 := fun n => (hs n).1
    let hstep : ∀ n, ∃ d : K, a (n + 1) = d ^ (p ^ n) * a n :=
      fun n => by obtain ⟨d, _, hd⟩ := hcompat n; exact ⟨d, hd⟩
    refine ⟨a, ha, hstep, ?_⟩
    exact (compatibleSourceClass_eq_original p a ha hstep f b
      (fun n => (hs n).2.1) (fun n => (hs n).2.2)).trans hq

end
end JoshiTeich.Act1Scene1.LocalKummer
