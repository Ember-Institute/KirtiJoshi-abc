import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-ROOT-TOWER
source: Joshi III compatible roots of 1+pStar*qroot and the associated
cohomology construction (3190--3208); algebraic Kummer construction.
fidelity: constructs compatible roots in an algebraically closed extension,
and the Galois ratio cocycle in the underlying inverse-limit group of
p-power roots of unity. Continuity, continuous cohomology, crystalline/BK
membership and comparison with the ordinary logarithm remain unproved.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]

structure RootTower (p : ℕ) (a : K) where
  root : ℕ → Ω
  root_zero : root 0 = algebraMap K Ω a
  root_succ : ∀ n, root (n + 1) ^ p = root n

section Construction
variable [IsAlgClosed Ω] (p : ℕ) (hp : 0 < p)

private def chooseRoot (x : Ω) : Ω := Classical.choose (IsAlgClosed.exists_pow_nat_eq x hp)

private theorem chooseRoot_pow (x : Ω) : chooseRoot p hp x ^ p = x :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq x hp)

def roots (a : K) : ℕ → Ω :=
  Nat.rec (algebraMap K Ω a) (fun _ x => chooseRoot p hp x)

def rootTower (a : K) : RootTower (Ω := Ω) p a where
  root := roots p hp a
  root_zero := rfl
  root_succ n := chooseRoot_pow p hp _

end Construction

namespace RootTower
variable {p : ℕ} {a : K} (R : RootTower (Ω := Ω) p a)

theorem root_pow_eq (n : ℕ) : R.root n ^ (p ^ n) = algebraMap K Ω a := by
  induction n with
  | zero => simpa using R.root_zero
  | succ n ih => rw [pow_succ', pow_mul, R.root_succ, ih]

theorem root_ne_zero (hp : 0 < p) (ha : a ≠ 0) (n : ℕ) : R.root n ≠ 0 := by
  intro h
  have hpow := R.root_pow_eq n
  rw [h, zero_pow (pow_pos hp n).ne'] at hpow
  exact ((map_ne_zero (algebraMap K Ω)).mpr ha) hpow.symm

def ratio (σ : Ω ≃ₐ[K] Ω) (n : ℕ) : Ω := σ (R.root n) / R.root n

theorem ratio_pow_eq_one (hp : 0 < p) (ha : a ≠ 0) (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    R.ratio σ n ^ (p ^ n) = 1 := by
  rw [ratio, div_pow, ← map_pow, R.root_pow_eq, σ.commutes,
    div_self ((map_ne_zero (algebraMap K Ω)).mpr ha)]

theorem ratio_succ_pow (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    R.ratio σ (n + 1) ^ p = R.ratio σ n := by
  rw [ratio, div_pow, ← map_pow, R.root_succ, ratio]

theorem ratio_mul (hp : 0 < p) (ha : a ≠ 0) (σ τ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    R.ratio (σ * τ) n = σ (R.ratio τ n) * R.ratio σ n := by
  have hn := R.root_ne_zero hp ha n
  have hs : σ (R.root n) ≠ 0 := by simpa only [map_zero] using σ.injective.ne hn
  change σ (τ (R.root n)) / R.root n =
    σ (τ (R.root n) / R.root n) * (σ (R.root n) / R.root n)
  rw [map_div₀]
  field_simp [hn, hs] <;> ring

def character (hp : 0 < p) (ha : a ≠ 0) (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    rootsOfUnity (p ^ n) Ω :=
  ⟨Units.mk0 (R.ratio σ n)
    (div_ne_zero (by simpa only [map_zero] using σ.injective.ne (R.root_ne_zero hp ha n))
      (R.root_ne_zero hp ha n)),
    (mem_rootsOfUnity' _ _).mpr (R.ratio_pow_eq_one hp ha σ n)⟩

end RootTower

/-- The underlying multiplicative inverse limit; no topology or Z_p module is supplied here. -/
def cyclotomicTateGroup (p : ℕ) (Ω : Type v) [Field Ω] : Subgroup (ℕ → Ωˣ) where
  carrier := {x | (∀ n, x n ^ (p ^ n) = 1) ∧ (∀ n, x (n + 1) ^ p = x n)}
  one_mem' := by constructor <;> intro n <;> simp
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro n; simp only [Pi.mul_apply, mul_pow, hx.1 n, hy.1 n, one_mul]
    · intro n; simp only [Pi.mul_apply, mul_pow, hx.2 n, hy.2 n]
  inv_mem' := by
    intro x hx
    constructor
    · intro n; simp only [Pi.inv_apply, inv_pow, hx.1 n, inv_one]
    · intro n; simp only [Pi.inv_apply, inv_pow, hx.2 n]

def tateAction (p : ℕ) (σ : Ω ≃ₐ[K] Ω) (x : cyclotomicTateGroup p Ω) :
    cyclotomicTateGroup p Ω :=
  ⟨fun n => σ • x.1 n, by
    constructor
    · intro n; rw [← smul_pow', x.2.1 n, smul_one]
    · intro n; rw [← smul_pow', x.2.2 n]⟩

instance tateMulDistribMulAction (p : ℕ) :
    MulDistribMulAction (Ω ≃ₐ[K] Ω) (cyclotomicTateGroup p Ω) where
  smul := tateAction p
  one_smul x := by apply Subtype.ext; funext n; exact one_smul _ _
  mul_smul σ τ x := by apply Subtype.ext; funext n; exact mul_smul σ τ (x.1 n)
  smul_one σ := by apply Subtype.ext; funext n; exact smul_one σ
  smul_mul σ x y := by apply Subtype.ext; funext n; exact smul_mul' σ (x.1 n) (y.1 n)

namespace RootTower
variable {p : ℕ} {a : K} (R : RootTower (Ω := Ω) p a) (hp : 0 < p) (ha : a ≠ 0)

def kummerCocycle (σ : Ω ≃ₐ[K] Ω) : cyclotomicTateGroup p Ω :=
  ⟨fun n => (R.character hp ha σ n).1, by
    constructor
    · intro n; exact (mem_rootsOfUnity _ _).mp (R.character hp ha σ n).2
    · intro n; apply Units.ext; exact R.ratio_succ_pow σ n⟩

theorem kummerCocycle_apply (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    ((R.kummerCocycle hp ha σ).1 n : Ω) = R.ratio σ n := rfl

theorem isMulCocycle_kummerCocycle : groupCohomology.IsMulCocycle₁ (R.kummerCocycle hp ha) := by
  intro σ τ
  apply Subtype.ext
  funext n
  apply Units.ext
  exact R.ratio_mul hp ha σ τ n

end RootTower

end
end JoshiTeich.Act1Scene1.LocalKummer
