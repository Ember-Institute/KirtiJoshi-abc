import Solutions.Source_ReferenceIutCor312CrystallineLog

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => (LocalGeometricFontaine.integerRing C)
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))
local notation "ι" => algebraMap (Ainf C p) (AinfInvertP C p)

private def thetaInField : Ainf C p →+* C :=
  (Subring.subtype 𝒪).comp θ

private theorem thetaInField_prime_unit : IsUnit (thetaInField C p (p : Ainf C p)) := by
  rw [map_natCast]
  exact (norm_pos_iff.mp
    (Fact.out : 0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1).1).isUnit

private def thetaLocalization : AinfInvertP C p →+* C :=
  Localization.awayLift (thetaInField C p) (p : Ainf C p) (thetaInField_prime_unit C p)

private theorem thetaLocalization_algebraMap (x : Ainf C p) :
    thetaLocalization C p (ι x) = thetaInField C p x :=
  IsLocalization.Away.lift_eq (p : Ainf C p) (thetaInField_prime_unit C p) x

variable [CharZero C]

private theorem thetaLocalization_gamma_mem_integerRing (n : ℕ) (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ) : thetaLocalization C p (gamma C p n x) ∈ 𝒪 := by
  have hθ : thetaInField C p x = 0 := by
    change (θ x : C) = 0
    rw [RingHom.mem_ker.mp hx, Subring.coe_zero]
  cases n with
  | zero =>
      have h := congrArg (thetaLocalization C p) (factorial_mul_gamma C p 0 x)
      have hOne : thetaLocalization C p (gamma C p 0 x) = 1 := by
        simpa only [map_mul, map_natCast, map_pow, Nat.factorial_zero, Nat.cast_one,
          one_mul, pow_zero, map_one] using h
      rw [hOne]
      exact Subring.one_mem _
  | succ n =>
      have h := congrArg (thetaLocalization C p) (factorial_mul_gamma C p (n + 1) x)
      simp only [map_mul, map_natCast, map_pow, thetaLocalization_algebraMap, hθ,
        zero_pow (Nat.succ_ne_zero n)] at h
      rw [(mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (n + 1).factorial_ne_zero)]
      exact Subring.zero_mem _

private theorem thetaLocalization_mem_integerRing (a : AinfInvertP C p) (ha : a ∈ A0 C p) :
    thetaLocalization C p a ∈ 𝒪 := by
  refine Algebra.adjoin_induction (p := fun z _ => thetaLocalization C p z ∈ 𝒪)
    ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨n, x, hx, rfl⟩
    exact thetaLocalization_gamma_mem_integerRing C p n x hx
  · intro x
    rw [thetaLocalization_algebraMap]
    exact (θ x).property
  · intro x y _ _ hx hy
    rw [map_add]
    exact Subring.add_mem _ hx hy
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subring.mul_mem _ hx hy

/-- The Fontaine map on the divided-power subalgebra takes values in the valuation ring. -/
def thetaA0 : A0 C p →+* 𝒪 :=
  (thetaLocalization C p).restrict (A0 C p) 𝒪 (thetaLocalization_mem_integerRing C p)

@[simp]
theorem thetaA0_algebraMap (x : Ainf C p) :
    thetaA0 C p (algebraMap (Ainf C p) (A0 C p) x) = θ x := by
  apply Subtype.ext
  exact thetaLocalization_algebraMap C p x

theorem thetaA0_logTerm (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) (n : ℕ) :
    (thetaA0 C p (DividedPowerLog.logTerm (fun m => gammaInOfMemKerSupPrime C p m x hx) n) : C) =
      (-1 : C) ^ n * (θ x : C) ^ (n + 1) / ((n + 1 : ℕ) : C) := by
  let f : A0 C p →+* C := (Subring.subtype 𝒪).comp (thetaA0 C p)
  change f _ = _
  have hMap (y : Ainf C p) : f (algebraMap (Ainf C p) (A0 C p) y) = (θ y : C) :=
    congrArg (fun a : 𝒪 => (a : C)) (thetaA0_algebraMap C p y)
  have hTerm := congrArg f (natCast_succ_mul_crystallineLogTerm C p x hx n)
  simp only [map_mul, map_natCast, map_neg, map_one, map_pow, hMap] at hTerm
  exact (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))).mpr
    ((mul_comm _ _).trans hTerm)

theorem thetaA0_logPartialSum (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) (N : ℕ) :
    (thetaA0 C p (DividedPowerLog.logPartialSum (fun m => gammaInOfMemKerSupPrime C p m x hx) N) : C) =
      ∑ n ∈ Finset.range N, (-1 : C) ^ n * (θ x : C) ^ (n + 1) / ((n + 1 : ℕ) : C) := by
  let f : A0 C p →+* C := (Subring.subtype 𝒪).comp (thetaA0 C p)
  change f _ = _
  rw [DividedPowerLog.logPartialSum, map_sum]
  exact Finset.sum_congr rfl fun n _ => thetaA0_logTerm C p x hx n

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
