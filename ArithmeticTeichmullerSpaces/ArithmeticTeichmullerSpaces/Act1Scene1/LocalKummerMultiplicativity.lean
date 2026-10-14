import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Linearity
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerMathlibCohomology

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-MULTIPLICATIVITY
source: Joshi III compatible local Kummer roots (3190--3208), with the
standard multiplicative Kummer map and cohomology scalar laws.
fidelity: multiplies root towers, proves the cocycle product formula, and
constructs a group homomorphism from base-field units to continuous H1.
Unit powers give natural-number multiples of the class. No BK identity is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]

namespace RootTower
variable {p : ℕ} {a b : K} (R : RootTower (Ω := Ω) p a) (S : RootTower (Ω := Ω) p b)

def mul : RootTower (Ω := Ω) p (a * b) where
  root n := R.root n * S.root n
  root_zero := by rw [R.root_zero, S.root_zero, map_mul]
  root_succ n := by rw [mul_pow, R.root_succ, S.root_succ]

theorem mul_root (n : ℕ) : (R.mul S).root n = R.root n * S.root n := rfl

theorem kummerCocycle_mul (hp : 0 < p) (ha : a ≠ 0) (hb : b ≠ 0) (σ : Ω ≃ₐ[K] Ω) :
    (R.mul S).kummerCocycle hp (mul_ne_zero ha hb) σ =
      R.kummerCocycle hp ha σ * S.kummerCocycle hp hb σ := by
  apply Subtype.ext
  funext n
  apply Units.ext
  change σ (R.root n * S.root n) / (R.root n * S.root n) =
    (σ (R.root n) / R.root n) * (σ (S.root n) / S.root n)
  rw [map_mul, mul_div_mul_comm]

end RootTower

def multiplyCocycles {p : ℕ} (f g : continuousCocycles (K := K) (Ω := Ω) p) :
    continuousCocycles (K := K) (Ω := Ω) p :=
  ⟨f.1 * g.1, by
    intro σ τ
    change f.1 (σ * τ) * g.1 (σ * τ) = σ • (f.1 τ * g.1 τ) * (f.1 σ * g.1 σ)
    rw [f.2 σ τ, g.2 σ τ, smul_mul']
    ac_rfl⟩

variable [Algebra.IsIntegral K Ω]

theorem mathlibClassOfCocycle_mul {p : ℕ}
    (f g : continuousCocycles (K := K) (Ω := Ω) p) :
    mathlibClassOfCocycle (multiplyCocycles f g) =
      mathlibClassOfCocycle f + mathlibClassOfCocycle g :=
  ContinuousH1Homogeneous.classOf_add _ _ _ (additiveCocycle_law f) (additiveCocycle_law g)

namespace RootTower
variable {p : ℕ} {a b : K} (R : RootTower (Ω := Ω) p a) (S : RootTower (Ω := Ω) p b)

theorem mathlibClass_mul (hp : 0 < p) (ha : a ≠ 0) (hb : b ≠ 0) :
    toMathlibH1 ((R.mul S).kummerClass hp (mul_ne_zero ha hb)) =
      toMathlibH1 (R.kummerClass hp ha) + toMathlibH1 (S.kummerClass hp hb) := by
  have he : (R.mul S).continuousCocycleValue hp (mul_ne_zero ha hb) =
      multiplyCocycles (R.continuousCocycleValue hp ha) (S.continuousCocycleValue hp hb) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro σ
    exact R.kummerCocycle_mul S hp ha hb σ
  change mathlibClassOfCocycle ((R.mul S).continuousCocycleValue hp (mul_ne_zero ha hb)) =
    mathlibClassOfCocycle (R.continuousCocycleValue hp ha) +
      mathlibClassOfCocycle (S.continuousCocycleValue hp hb)
  rw [he, mathlibClassOfCocycle_mul]

end RootTower

variable [IsAlgClosed Ω] (p : ℕ) (hp : 0 < p)

def kummerHom : Kˣ →* Multiplicative (continuousCohomology 1 (tateTopRep (K := K) (Ω := Ω) p)) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd
    (toMathlibH1 ((rootTower (Ω := Ω) p hp (a : K)).kummerClass hp a.ne_zero))) (by
    intro a b
    let R := rootTower (Ω := Ω) p hp (a : K)
    let S := rootTower (Ω := Ω) p hp (b : K)
    have he := (rootTower (Ω := Ω) p hp ((a * b : Kˣ) : K)).kummerClass_eq
      (R.mul S) hp (a * b).ne_zero
    change toMathlibH1 ((rootTower (Ω := Ω) p hp ((a * b : Kˣ) : K)).kummerClass
      hp (a * b).ne_zero) = toMathlibH1 (R.kummerClass hp a.ne_zero) +
        toMathlibH1 (S.kummerClass hp b.ne_zero)
    exact (congrArg toMathlibH1 he).trans (R.mathlibClass_mul S hp a.ne_zero b.ne_zero))

theorem kummerHom_apply (a : Kˣ) :
    (kummerHom (K := K) (Ω := Ω) p hp a).toAdd =
      toMathlibH1 ((rootTower (Ω := Ω) p hp (a : K)).kummerClass hp a.ne_zero) := rfl

theorem kummerHom_pow (a : Kˣ) (n : ℕ) :
    (kummerHom (K := K) (Ω := Ω) p hp (a ^ n)).toAdd =
      n • (kummerHom (K := K) (Ω := Ω) p hp a).toAdd := by
  simpa only [toAdd_pow] using
    congrArg Multiplicative.toAdd (map_pow (kummerHom (K := K) (Ω := Ω) p hp) a n)

end
end JoshiTeich.Act1Scene1.LocalKummer
