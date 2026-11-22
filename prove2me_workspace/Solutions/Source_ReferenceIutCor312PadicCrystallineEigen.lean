import Solutions.Source_ReferenceIutCor312CrystallineLogEigen
import Solutions.Source_ReferenceIutCor312PadicKummerCrystallineBridge

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

noncomputable section

variable (p : ℕ) [Fact p.Prime]

local notation "Cₚ" => PadicComplex p
local notation "𝒪ₚ" => LocalGeometricFontaine.integerRing Cₚ

/-- The image under crystalline Frobenius equals multiplication by the prime. -/
def isPadicFrobeniusPrimeEigen (x : PadicACris p) : Prop :=
  let y : ACris Cₚ p := x
  frobeniusACris Cₚ p y = (p : ACris Cₚ p) * y

theorem isPadicFrobeniusPrimeEigen_padicKummerLog
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {a : K}
    (R : LocalKummer.RootTower (Ω := Ω) p a) (j : Ω →+* Cₚ)
    (ha : ‖j (algebraMap K Ω a)‖ ≤ 1)
    (hu : ∃ r : 𝒪ₚ, j (algebraMap K Ω a) = 1 + (p : Cₚ) * (r : Cₚ)) :
    isPadicFrobeniusPrimeEigen p (padicKummerLog p R j ha hu) :=
  frobeniusACris_kummerLogOfExists_eq_prime_mul Cₚ p R j ha hu

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
