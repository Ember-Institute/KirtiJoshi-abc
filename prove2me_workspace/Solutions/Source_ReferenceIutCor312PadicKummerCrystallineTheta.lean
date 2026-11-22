import Solutions.Source_ReferenceIutCor312KummerCrystallineTheta
import Solutions.Source_ReferenceIutCor312PadicKummerCrystallineBridge

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open scoped Valued

noncomputable section

variable (p : ℕ) [Fact p.Prime]

local notation "Cₚ" => PadicComplex p
local notation "𝒪ₚ" => LocalGeometricFontaine.integerRing Cₚ

/-- The Fontaine image of a standard crystalline element, viewed in the coefficient field. -/
def isPadicThetaValue (x : PadicACris p) (value : Cₚ) : Prop :=
  let y : ACris Cₚ p := x
  (thetaCrystalline Cₚ p y : Cₚ) = value

/-- The Fontaine image of a standard crystalline Kummer logarithm is the embedded
ordinary logarithm of the same unit. -/
theorem isPadicThetaValue_padicKummerLog
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [Valued k (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
    [CharZero k] [CompleteSpace k] {u : k}
    (R : LocalKummer.RootTower (Ω := Ω) p u) (j : Ω →+* Cₚ)
    (hj : Continuous (j.comp (algebraMap k Ω)))
    (ha : ‖j (algebraMap k Ω u)‖ ≤ 1)
    (hu : ∃ r : 𝒪ₚ, j (algebraMap k Ω u) = 1 + (p : Cₚ) * (r : Cₚ))
    (hpk : ‖(p : k)‖ < 1) (hprincipal : ‖u - 1‖ < 1) :
    isPadicThetaValue p (padicKummerLog (K := k) (Ω := Ω) (a := u) p R j ha hu)
      (j (algebraMap k Ω (LocalPadicLog.padicLog u))) :=
  @thetaCrystalline_kummerLogOfExists_eq_padicLog Cₚ (PadicComplex.normedField p)
    (PadicComplex.isUltrametricDist p) (inferInstance : CompleteSpace Cₚ)
    (PadicComplex.charZero p) p _ (PadicTiltField.primeNormFact p) (PadicComplex.isAlgClosed p)
    k Ω _ _ _ _ _ _ _ u R j hj ha hu hpk hprincipal

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
