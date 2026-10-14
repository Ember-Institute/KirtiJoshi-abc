import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerH1Equivalence
import Mathlib.FieldTheory.Galois.Infinite

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-ROOT-DESCENT
source: Kummer coboundaries and fixed-field descent, Joshi III (3190--3208).
fidelity: the standard integral Kummer class vanishes exactly when a
compatible p-power root tower exists in the base field. Descent uses the
actual Galois fixed-field theorem, with no supplied root or descent certificate.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.RootTower
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable {p : ℕ} {a : K} (R : RootTower (Ω := Ω) p a)

def fromBase (S : RootTower (K := K) (Ω := K) p a) : RootTower (Ω := Ω) p a where
  root n := algebraMap K Ω (S.root n)
  root_zero := by rw [S.root_zero, Algebra.algebraMap_self_apply]
  root_succ n := by rw [← map_pow, S.root_succ]

theorem fromBase_cocycle (S : RootTower (K := K) (Ω := K) p a)
    (hp : 0 < p) (ha : a ≠ 0) (σ : Ω ≃ₐ[K] Ω) :
    (fromBase (Ω := Ω) S).kummerCocycle hp ha σ = 1 := by
  apply Subtype.ext
  funext n
  apply Units.ext
  change σ (algebraMap K Ω (S.root n)) / algebraMap K Ω (S.root n) = 1
  rw [σ.commutes, div_self]
  exact (map_ne_zero (algebraMap K Ω)).mpr (S.root_ne_zero hp ha n)

def corrected (t : cyclotomicTateGroup p Ω) : RootTower (Ω := Ω) p a where
  root n := R.root n / (t.1 n : Ω)
  root_zero := by
    have ht := congrArg (fun z : Ωˣ => (z : Ω)) (t.2.1 0)
    simp only [pow_zero, pow_one, Units.val_one] at ht
    rw [R.root_zero, ht, div_one]
  root_succ n := by
    rw [div_pow, R.root_succ]
    exact congrArg (fun z : Ωˣ => R.root n / (z : Ω)) (t.2.2 n)

theorem corrected_fixed (hp : 0 < p) (ha : a ≠ 0) (t : cyclotomicTateGroup p Ω)
    (ht : ∀ σ : Ω ≃ₐ[K] Ω, R.kummerCocycle hp ha σ = σ • t / t)
    (σ : Ω ≃ₐ[K] Ω) (n : ℕ) : σ ((R.corrected t).root n) = (R.corrected t).root n := by
  have he := congrArg (fun z : cyclotomicTateGroup p Ω => (z.1 n : Ω)) (ht σ)
  simp only [Subgroup.coe_div, Pi.div_apply, Units.val_div_eq_div_val] at he
  change σ (R.root n) / R.root n = σ (t.1 n : Ω) / (t.1 n : Ω) at he
  have hR := R.root_ne_zero hp ha n
  have ht0 := (t.1 n).ne_zero
  have hs0 : σ (t.1 n : Ω) ≠ 0 := by simpa only [map_zero] using σ.injective.ne ht0
  change σ (R.root n / (t.1 n : Ω)) = R.root n / (t.1 n : Ω)
  rw [map_div₀]
  field_simp [hR, ht0] at he
  apply (div_eq_div_iff hs0 ht0).mpr
  exact he

variable [IsGalois K Ω]

theorem exists_baseTower_of_coboundary (hp : 0 < p) (ha : a ≠ 0)
    (t : cyclotomicTateGroup p Ω)
    (ht : ∀ σ : Ω ≃ₐ[K] Ω, R.kummerCocycle hp ha σ = σ • t / t) :
    Nonempty (RootTower (K := K) (Ω := K) p a) := by
  have hdesc (n : ℕ) : ∃ b : K, algebraMap K Ω b = (R.corrected t).root n :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr (fun σ => R.corrected_fixed hp ha t ht σ n)
  choose b hb using hdesc
  refine ⟨⟨b, ?_, fun n => ?_⟩⟩
  · rw [Algebra.algebraMap_self_apply]
    apply (algebraMap K Ω).injective
    rw [hb, (R.corrected t).root_zero]
  · apply (algebraMap K Ω).injective
    rw [map_pow, hb, hb, (R.corrected t).root_succ]

variable [Algebra.IsIntegral K Ω] [Fact p.Prime]

theorem padicClass_eq_zero_iff_baseTower (ha : a ≠ 0) :
    padicClassOfCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos ha) = 0 ↔
      Nonempty (RootTower (K := K) (Ω := K) p a) := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (padicClassOfCocycle_eq_zero_iff p _).mp h
    exact R.exists_baseTower_of_coboundary (Fact.out : p.Prime).pos ha t ht
  · rintro ⟨S⟩
    apply (padicClassOfCocycle_eq_zero_iff p _).mpr
    let T := fromBase (Ω := Ω) S
    let t := T.rootChange R (Fact.out : p.Prime).pos ha
    refine ⟨t, fun σ => ?_⟩
    have h := T.kummerCocycle_div_eq R (Fact.out : p.Prime).pos ha σ
    rw [fromBase_cocycle, div_one] at h
    exact h

theorem exists_root_of_padicClass_eq_zero (ha : a ≠ 0)
    (h : padicClassOfCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos ha) = 0)
    (n : ℕ) : ∃ b : K, b ^ (p ^ n) = a := by
  obtain ⟨S⟩ := (R.padicClass_eq_zero_iff_baseTower ha).mp h
  exact ⟨S.root n, by simpa only [Algebra.algebraMap_self_apply] using S.root_pow_eq n⟩

theorem padicClass_ne_zero_of_no_root (ha : a ≠ 0) (n : ℕ)
    (h : ¬ ∃ b : K, b ^ (p ^ n) = a) :
    padicClassOfCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos ha) ≠ 0 :=
  fun hz => h (R.exists_root_of_padicClass_eq_zero ha hz n)

end
end JoshiTeich.Act1Scene1.LocalKummer.RootTower
