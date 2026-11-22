import Solutions.Source_ReferenceIutCor312CrystallineLog

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

/-- The integral crystalline completion with the prime inverted. -/
abbrev ACrisInvertP := Localization.Away (p : ACris C p)

local notation "ι" => algebraMap (ACris C p) (ACrisInvertP C p)

theorem ACrisInvertP_prime_isUnit : IsUnit (p : ACrisInvertP C p) := by
  simpa only [map_natCast] using
    IsLocalization.Away.algebraMap_isUnit (S := ACrisInvertP C p) (p : ACris C p)

private theorem mapACrisInvertP_prime_isUnit (f : ACris C p →+* ACris C p) :
    IsUnit (((ι).comp f) (p : ACris C p)) := by
  rw [RingHom.comp_apply, map_natCast, map_natCast]
  exact ACrisInvertP_prime_isUnit C p

/-- A ring endomorphism of the integral completion extends after inverting the prime. -/
def mapACrisInvertP (f : ACris C p →+* ACris C p) : ACrisInvertP C p →+* ACrisInvertP C p :=
  Localization.awayLift ((ι).comp f) (p : ACris C p) (mapACrisInvertP_prime_isUnit C p f)

@[simp]
theorem mapACrisInvertP_algebraMap (f : ACris C p →+* ACris C p) (x : ACris C p) :
    mapACrisInvertP C p f (ι x) = ι (f x) :=
  IsLocalization.Away.lift_eq (p : ACris C p) (mapACrisInvertP_prime_isUnit C p f) x

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
