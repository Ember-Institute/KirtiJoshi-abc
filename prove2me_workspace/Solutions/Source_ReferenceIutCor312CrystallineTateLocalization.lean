import Solutions.Source_ReferenceIutCor312LocalizationAwayLift
import Solutions.Source_ReferenceIutCor312CrystallineTateGalois

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope LocalKummer

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω ≃ₐ[K] Ω)
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω →+* C)
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "t" => mappedTateBasisPeriod C p ι
local notation "j" => algebraMap B Bₜ

private def galoisToTateLocalization (σ : G) : B →+* Bₜ :=
  (j : B →+* Bₜ).comp (mapACrisInvertP C p (extendGaloisACris (K := K) p σ))

private theorem galoisImageTatePeriod_isUnit (σ : G) :
    IsUnit (galoisToTateLocalization p σ t) := by
  let u : (PadicInt p)ˣ := Cyclotomic.character p σ
  let a : B := padicIntMapACrisInvertP p C (u : PadicInt p)
  have ha : IsUnit (j a) :=
    (u.isUnit.map (padicIntMapACrisInvertP p C)).map (j : B →+* Bₜ)
  have hperiod : galoisToTateLocalization p σ t = (j a) * (j t) :=
    (congrArg (j : B →+* Bₜ) (extendGaloisACrisInvertP_mappedTateBasisPeriod (K := K) p σ)).trans
      (map_mul (j : B →+* Bₜ) a t)
  exact hperiod.symm ▸ ha.mul (ACrisInvertTatePeriod_period_isUnit C p ι)

/-- The original Galois action on crystalline coefficients extends after inverting
the original Tate period. -/
def extendGaloisACrisInvertTatePeriodHom (σ : G) : Bₜ →+* Bₜ :=
  LocalizationAway.liftEndomorphism (R := B) (S := Bₜ) t (galoisToTateLocalization p σ)
    (galoisImageTatePeriod_isUnit p σ)

@[simp]
theorem extendGaloisACrisInvertTatePeriodHom_algebraMap (σ : G) (z : B) :
    extendGaloisACrisInvertTatePeriodHom p σ (j z) =
      j (mapACrisInvertP C p (extendGaloisACris p σ) z) :=
  show extendGaloisACrisInvertTatePeriodHom p σ (j z) = galoisToTateLocalization p σ z from
    LocalizationAway.liftEndomorphism_algebraMap (R := B) (S := Bₜ) t (galoisToTateLocalization p σ)
      (galoisImageTatePeriod_isUnit p σ) z

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
