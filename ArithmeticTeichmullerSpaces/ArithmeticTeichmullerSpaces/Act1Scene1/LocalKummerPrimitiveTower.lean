import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicModule
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-PRIMITIVE-TOWER
source: the compatible primitive roots underlying Z_p(1) in Joshi III (3190--3208).
fidelity: constructs a compatible sequence whose nth level has exact order p^n
in an algebraically closed characteristic-zero field. No compatible generator
is supplied by a caller.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.TateBasis
universe v
noncomputable section
variable {p : ℕ} [Fact p.Prime] {Ω : Type v} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]

def primitiveP : Ω := Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot Ω p)

theorem primitiveP_spec : IsPrimitiveRoot (primitiveP (p := p) (Ω := Ω)) p :=
  Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot Ω p)

def positiveTower : RootTower (K := Ω) (Ω := Ω) p (primitiveP (p := p) (Ω := Ω)) :=
  rootTower p (Fact.out : p.Prime).pos _

def generatorValues : ℕ → Ω
  | 0 => 1
  | n + 1 => (positiveTower (p := p) (Ω := Ω)).root n

theorem generatorValues_isPrimitive (n : ℕ) :
    IsPrimitiveRoot (generatorValues (p := p) (Ω := Ω) n) (p ^ n) := by
  cases n with
  | zero => simpa only [generatorValues, pow_zero] using (IsPrimitiveRoot.one (M := Ω))
  | succ n =>
    apply IsPrimitiveRoot.iff_orderOf.mpr
    apply orderOf_eq_prime_pow
    · change (positiveTower (p := p) (Ω := Ω)).root n ^ (p ^ n) ≠ 1
      rw [RootTower.root_pow_eq, Algebra.algebraMap_self_apply]
      exact primitiveP_spec.ne_one (Fact.out : p.Prime).one_lt
    · change (positiveTower (p := p) (Ω := Ω)).root n ^ (p ^ (n + 1)) = 1
      rw [pow_succ, pow_mul, RootTower.root_pow_eq, Algebra.algebraMap_self_apply]
      exact primitiveP_spec.pow_eq_one

theorem generatorValues_succ_pow (n : ℕ) :
    generatorValues (p := p) (Ω := Ω) (n + 1) ^ p = generatorValues (p := p) (Ω := Ω) n := by
  cases n with
  | zero =>
    change (positiveTower (p := p) (Ω := Ω)).root 0 ^ p = 1
    rw [RootTower.root_zero, Algebra.algebraMap_self_apply]
    exact primitiveP_spec.pow_eq_one
  | succ n => exact (positiveTower (p := p) (Ω := Ω)).root_succ n

def generator : cyclotomicTateGroup p Ω :=
  ⟨fun n => Units.mk0 (generatorValues n)
    ((generatorValues_isPrimitive (p := p) (Ω := Ω) n).isUnit
      (pow_pos (Fact.out : p.Prime).pos n).ne').ne_zero, by
    constructor
    · intro n
      apply Units.ext
      exact (generatorValues_isPrimitive (p := p) (Ω := Ω) n).pow_eq_one
    · intro n
      apply Units.ext
      exact generatorValues_succ_pow n⟩

theorem generator_isPrimitive (n : ℕ) :
    IsPrimitiveRoot ((generator (p := p) (Ω := Ω)).1 n) (p ^ n) :=
  IsPrimitiveRoot.coe_units_iff.mp (generatorValues_isPrimitive n)

end
end JoshiTeich.Act1Scene1.LocalKummer.TateBasis
