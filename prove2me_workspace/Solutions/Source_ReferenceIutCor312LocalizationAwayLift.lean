import Mathlib.RingTheory.Localization.Away.Basic

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalizationAway

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Lift a ring map into a localization to an endomorphism of that localization. -/
noncomputable def liftEndomorphism (t : R) [IsLocalization.Away t S]
    (f : R →+* S) (ht : IsUnit (f t)) : S →+* S :=
  IsLocalization.Away.lift (S := S) t ht

theorem liftEndomorphism_algebraMap (t : R) [IsLocalization.Away t S]
    (f : R →+* S) (ht : IsUnit (f t)) (z : R) :
    liftEndomorphism t f ht (algebraMap R S z) = f z :=
  IsLocalization.Away.lift_eq (S := S) t ht z

end JoshiTeich.Act1Scene1.LocalizationAway
