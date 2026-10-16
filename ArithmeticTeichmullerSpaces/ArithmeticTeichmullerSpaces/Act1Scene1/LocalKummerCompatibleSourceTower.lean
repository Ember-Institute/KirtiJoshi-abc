import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCohomology

/-!
source-id: JT-SCENE1-COMPATIBLE-KUMMER-SOURCE-TOWER
source: compatible representatives of K*/(K*)^(p^n), algebraic closure
root extraction and the original Tate inverse limit; Joshi III 3190--3236.
fidelity: constructs roots of a varying compatible base-field source family.
Adjacent roots differ by the supplied representative correction in K, which
cancels from Galois ratios and produces an actual continuous Tate cocycle.
No compatible roots or cocycle are assumed as an input.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]

/-- Root compatibility permits the base-field correction between adjacent sources. -/
structure CompatibleSourceTower (p : ℕ) (a : ℕ → K) where
  correction : ℕ → K
  root : ℕ → Ω
  root_pow_eq : ∀ n, root n ^ (p ^ n) = algebraMap K Ω (a n)
  root_succ : ∀ n, root (n + 1) ^ p = algebraMap K Ω (correction n) * root n

namespace CompatibleSourceTower
variable {p : ℕ} {a : ℕ → K}

def ofCompatible [IsAlgClosed Ω] (hp : 0 < p)
    (hstep : ∀ n, ∃ d : K, a (n + 1) = d ^ (p ^ n) * a n) :
    CompatibleSourceTower (Ω := Ω) p a := by
  choose d hd using hstep
  let s : Ω → Ω := fun x => Classical.choose (IsAlgClosed.exists_pow_nat_eq x hp)
  have hs (x : Ω) : s x ^ p = x := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq x hp)
  let r : ℕ → Ω := Nat.rec (algebraMap K Ω (a 0))
    (fun n x => s (algebraMap K Ω (d n) * x))
  have hr (n : ℕ) : r (n + 1) ^ p = algebraMap K Ω (d n) * r n := hs _
  refine ⟨d, r, ?_, hr⟩
  intro n
  induction n with
  | zero => simp only [pow_zero, pow_one]; rfl
  | succ n ih =>
    rw [pow_succ', pow_mul, hr, mul_pow, ih, ← map_pow, ← map_mul, ← hd n]

variable (R : CompatibleSourceTower (Ω := Ω) p a)
variable [Fact p.Prime]

theorem root_ne_zero (ha : ∀ n, a n ≠ 0) (n : ℕ) : R.root n ≠ 0 := by
  intro hz
  have h := R.root_pow_eq n
  have hm : algebraMap K Ω (a n) ≠ 0 := (map_ne_zero (algebraMap K Ω)).mpr (ha n)
  rw [hz, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at h
  exact hm h.symm

def ratio (σ : Ω ≃ₐ[K] Ω) (n : ℕ) : Ω := σ (R.root n) / R.root n

theorem ratio_pow_eq_one (ha : ∀ n, a n ≠ 0) (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    R.ratio σ n ^ (p ^ n) = 1 := by
  rw [ratio, div_pow, ← map_pow, R.root_pow_eq, σ.commutes,
    div_self ((map_ne_zero (algebraMap K Ω)).mpr (ha n))]

theorem ratio_succ_pow (ha : ∀ n, a n ≠ 0) (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    R.ratio σ (n + 1) ^ p = R.ratio σ n := by
  have hd : R.correction n ≠ 0 := by
    intro hz
    have h := R.root_succ n
    rw [hz, map_zero, zero_mul] at h
    exact pow_ne_zero p (R.root_ne_zero ha (n + 1)) h
  rw [ratio, div_pow, ← map_pow, R.root_succ, map_mul, σ.commutes, ratio,
    mul_div_mul_left _ _ ((map_ne_zero (algebraMap K Ω)).mpr hd)]

theorem ratio_mul (ha : ∀ n, a n ≠ 0) (σ τ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    R.ratio (σ * τ) n = σ (R.ratio τ n) * R.ratio σ n := by
  have hn := R.root_ne_zero ha n
  have hs : σ (R.root n) ≠ 0 := by simpa only [map_zero] using σ.injective.ne hn
  change σ (τ (R.root n)) / R.root n =
    σ (τ (R.root n) / R.root n) * (σ (R.root n) / R.root n)
  rw [map_div₀]
  field_simp [hn, hs] <;> ring

def cocycle (ha : ∀ n, a n ≠ 0) (σ : Ω ≃ₐ[K] Ω) : cyclotomicTateGroup p Ω :=
  ⟨fun n => Units.mk0 (R.ratio σ n)
      (div_ne_zero (by simpa only [map_zero] using σ.injective.ne (R.root_ne_zero ha n))
        (R.root_ne_zero ha n)), by
    constructor
    · intro n; apply Units.ext; exact R.ratio_pow_eq_one ha σ n
    · intro n; apply Units.ext; exact R.ratio_succ_pow ha σ n⟩

theorem cocycle_law (ha : ∀ n, a n ≠ 0) :
    groupCohomology.IsMulCocycle₁ (R.cocycle ha) := by
  intro σ τ
  apply Subtype.ext
  funext n
  apply Units.ext
  exact R.ratio_mul ha σ τ n

variable [Algebra.IsIntegral K Ω]

theorem continuous_cocycle (ha : ∀ n, a n ≠ 0) : Continuous (R.cocycle ha) := by
  apply (continuous_tate_iff_level_locallyConstant _).mpr
  intro n
  have h : IsLocallyConstant (fun σ : Ω ≃ₐ[K] Ω => R.ratio σ n) :=
    (galoisEval_isLocallyConstant (R.root n)).comp (fun x => x / R.root n)
  exact IsLocallyConstant.desc _ (fun x : Ωˣ => (x : Ω)) h Units.val_injective

def continuousCocycleValue (ha : ∀ n, a n ≠ 0) :
    continuousCocycles (K := K) (Ω := Ω) p :=
  ⟨⟨R.cocycle ha, R.continuous_cocycle ha⟩, R.cocycle_law ha⟩

end CompatibleSourceTower
end
end JoshiTeich.Act1Scene1.LocalKummer
