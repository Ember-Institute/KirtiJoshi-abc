import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichFrobenius

/-!
source-id: JT-SCENE1-WITT-FROBENIUS-PRESENTATION
source: Joshi II `se:ff-rings`, Frobenius on bounded integral Witt
localizations; the original denominator p times a Teichmuller element.
fidelity: transforms an original denominator-power presentation under any
ring homomorphism with the proved Witt Frobenius inclusion law. The new
exponent is p times the old exponent, and the numerator has the explicit
p-power correction. It also proves uniqueness for a fixed presentation
and records existence from the localization universal property. The
original carrier, denominator and maps are retained. No invertibility of
the Frobenius map, norm law or comparison certificate is assumed.
Original proofs; no reference implementation copied.
boundary: algebraic presentations only; concrete comparison, completion
and paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.WittFrobeniusPresentation

open WittPrimeTeichLocalization
noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable {R : Type*} [CommRing R]

theorem presentation_unique (r : R) (m : ℕ) (a : WittVector p R)
    {x y : Ring p r}
    (hx : x * algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ m =
      algebraMap (WittVector p R) (Ring p r) a)
    (hy : y * algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ m =
      algebraMap (WittVector p R) (Ring p r) a) :
    x = y :=
  ((IsLocalization.Away.algebraMap_isUnit (denominator p r)
    (S := Ring p r)).pow m).mul_right_cancel (hx.trans hy.symm)

theorem exists_presentation (r : R) (x : Ring p r) :
    ∃ (m : ℕ) (a : WittVector p R),
      x * algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ m =
        algebraMap (WittVector p R) (Ring p r) a :=
  IsLocalization.Away.surj (denominator p r) x

variable [CharP R p]

def transform (m : ℕ) (a : WittVector p R) : WittVector p R :=
  ((p : WittVector p R) ^ (p - 1)) ^ m * WittVector.frobenius a

theorem denominator_pow (r : R) :
    denominator p r ^ p =
      (p : WittVector p R) ^ (p - 1) * WittVector.frobenius (denominator p r) := by
  rw [denominator, map_mul, map_natCast,
    WittFrobeniusTeichmullerRigidity.frobenius_teichmuller, mul_pow]
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]

theorem map_presentation (r : R) (F : Ring p r →+* Ring p r)
    (hF : ∀ a : WittVector p R,
      F (algebraMap (WittVector p R) (Ring p r) a) =
        algebraMap (WittVector p R) (Ring p r) (WittVector.frobenius a))
    (x : Ring p r) (m : ℕ) (a : WittVector p R)
    (hx : x * algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ m =
      algebraMap (WittVector p R) (Ring p r) a) :
    F x * algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ (p * m) =
      algebraMap (WittVector p R) (Ring p r) (transform p m a) := by
  have hbase : F x *
      algebraMap (WittVector p R) (Ring p r)
        (WittVector.frobenius (denominator p r)) ^ m =
      algebraMap (WittVector p R) (Ring p r) (WittVector.frobenius a) := by
    have h := congrArg F hx
    rw [map_mul, map_pow, hF, hF] at h
    exact h
  have hd :
      algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ p =
        algebraMap (WittVector p R) (Ring p r) ((p : WittVector p R) ^ (p - 1)) *
          algebraMap (WittVector p R) (Ring p r)
            (WittVector.frobenius (denominator p r)) := by
    rw [← map_pow, denominator_pow, map_mul]
  calc
    F x * algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ (p * m) =
        F x * (algebraMap (WittVector p R) (Ring p r) (denominator p r) ^ p) ^ m := by
      rw [pow_mul]
    _ = F x *
        (algebraMap (WittVector p R) (Ring p r) ((p : WittVector p R) ^ (p - 1)) *
          algebraMap (WittVector p R) (Ring p r)
            (WittVector.frobenius (denominator p r))) ^ m := by rw [hd]
    _ = algebraMap (WittVector p R) (Ring p r) ((p : WittVector p R) ^ (p - 1)) ^ m *
        (F x * algebraMap (WittVector p R) (Ring p r)
          (WittVector.frobenius (denominator p r)) ^ m) := by
      rw [mul_pow]
      ac_rfl
    _ = algebraMap (WittVector p R) (Ring p r) ((p : WittVector p R) ^ (p - 1)) ^ m *
        algebraMap (WittVector p R) (Ring p r) (WittVector.frobenius a) := by
      rw [hbase]
    _ = algebraMap (WittVector p R) (Ring p r) (transform p m a) := by
      simp only [transform, map_mul, map_pow]

end
end JoshiTeich.Act1Scene1.WittFrobeniusPresentation
