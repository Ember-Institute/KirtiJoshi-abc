import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRootDescent

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-TOWER-POWERS
source: powers of compatible Kummer roots, Joshi III (3190--3236).
fidelity: powers a root tower and identifies its actual cocycle with the
pointwise power. This supplies a concrete integral tower after clearing a
rational coboundary denominator.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.RootTower
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable {p : ℕ} {a : K} (R : RootTower (Ω := Ω) p a)

def pow (m : ℕ) : RootTower (Ω := Ω) p (a ^ m) where
  root n := R.root n ^ m
  root_zero := by rw [R.root_zero, map_pow]
  root_succ n := by rw [← pow_mul, Nat.mul_comm, pow_mul, R.root_succ]

theorem pow_cocycle (m : ℕ) (hp : 0 < p) (ha : a ≠ 0) (σ : Ω ≃ₐ[K] Ω) :
    (R.pow m).kummerCocycle hp (pow_ne_zero m ha) σ = R.kummerCocycle hp ha σ ^ m := by
  apply Subtype.ext
  funext n
  apply Units.ext
  change σ (R.root n ^ m) / (R.root n ^ m) = (σ (R.root n) / R.root n) ^ m
  rw [map_pow, div_pow]

end
end JoshiTeich.Act1Scene1.LocalKummer.RootTower
