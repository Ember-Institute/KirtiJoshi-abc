import Solutions.Source_ReferenceIutCor312CrystallineLogEigen
import Solutions.Source_ReferenceIutCor312LocalizationAwayLift
import Solutions.Source_ReferenceIutCor312MappedTatePeriod

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open LocalKummer

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (j : Ω →+* C)

local notation "A" => ACris C p
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p j
local notation "t" => mappedTateBasisPeriod C p j
local notation "i" => algebraMap A B
local notation "k" => algebraMap B Bₜ
local notation "φ" => frobeniusACris C p
local notation "φₚ" => mapACrisInvertP C p φ

private theorem map_natCast_mul {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (n : ℕ) (x : R) :
    f ((n : R) * x) = (n : S) * f x :=
  (map_mul f (n : R) x).trans
    (congrArg (fun c : S => c * f x) (map_natCast f n))

theorem ACrisInvertTatePeriod_prime_isUnit : IsUnit (p : Bₜ) :=
  (map_natCast (k : B →+* Bₜ) p) ▸
    ((ACrisInvertP_prime_isUnit C p).map (k : B →+* Bₜ))

private def frobeniusToTateLocalization : B →+* Bₜ :=
  (k : B →+* Bₜ).comp φₚ

private theorem frobeniusToTateLocalization_eigen (x : A) (hx : φ x = (p : A) * x) :
    frobeniusToTateLocalization C p j (i x) = (p : Bₜ) * k (i x) := by
  let f : A →+* Bₜ := (k : B →+* Bₜ).comp (i : A →+* B)
  have hmap : k (φₚ (i x)) = f (φ x) :=
    congrArg (k : B →+* Bₜ) (mapACrisInvertP_algebraMap C p φ x)
  exact hmap.trans ((congrArg f hx).trans (map_natCast_mul f p x))

local notation "ε" => mapCyclotomicTateGroup p j (TateBasis.generator (p := p) (Ω := Ω))

private theorem frobeniusImageTatePeriod_isUnit :
    IsUnit (frobeniusToTateLocalization C p j t) := by
  have ht : frobeniusToTateLocalization C p j t = (p : Bₜ) * k t :=
    frobeniusToTateLocalization_eigen C p j (cyclotomicLog C p ε)
      (frobeniusACris_cyclotomicLog_eq_prime_mul C p ε)
  exact ht.symm ▸ (ACrisInvertTatePeriod_prime_isUnit C p j).mul
    (ACrisInvertTatePeriod_period_isUnit C p j)

/-- Crystalline Frobenius extends after inverting the prime and the image of
the period of the original Tate basis. -/
def frobeniusACrisInvertTatePeriod : Bₜ →+* Bₜ :=
  LocalizationAway.liftEndomorphism (R := B) (S := Bₜ) t
    (frobeniusToTateLocalization C p j) (frobeniusImageTatePeriod_isUnit C p j)

@[simp]
theorem frobeniusACrisInvertTatePeriod_algebraMap (z : B) :
    frobeniusACrisInvertTatePeriod C p j (k z) = k (φₚ z) :=
  LocalizationAway.liftEndomorphism_algebraMap (R := B) (S := Bₜ) t
    (frobeniusToTateLocalization C p j) (frobeniusImageTatePeriod_isUnit C p j) z

/-- The image of an integral crystalline Frobenius eigenvector with eigenvalue
the prime has the same eigenvalue in the localization. -/
theorem frobeniusACrisInvertTatePeriod_eigen (x : A) (hx : φ x = (p : A) * x) :
    frobeniusACrisInvertTatePeriod C p j (k (i x)) = (p : Bₜ) * k (i x) :=
  (frobeniusACrisInvertTatePeriod_algebraMap C p j (i x)).trans
    (frobeniusToTateLocalization_eigen C p j x hx)

theorem frobeniusACrisInvertTatePeriod_mappedTateBasisPeriod :
    frobeniusACrisInvertTatePeriod C p j (k t) = (p : Bₜ) * k t :=
  frobeniusACrisInvertTatePeriod_eigen C p j (cyclotomicLog C p ε)
    (frobeniusACris_cyclotomicLog_eq_prime_mul C p ε)

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
