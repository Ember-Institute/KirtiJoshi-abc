import Solutions.Source_ReferenceIutCor312CrystallineLog
import Solutions.Source_ReferenceIutCor312CyclotomicFirstOrder

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue
open scoped BigOperators

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "A" => Ainf C p
local notation "B" => AinfInvertP C p
local notation "ι" => algebraMap A B
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))
local notation "ξ" => fontainePrimitive C p
local notation "J" => (Ideal.span {(ι ξ) ^ 2} : Ideal B)
local notation "q" => Ideal.Quotient.mk J
local notation "I" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))

omit [CompleteSpace C] [IsAlgClosed C] in
private theorem gamma_zero (x : A) : gamma C p 0 x = 1 := by
  simpa only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero] using
    factorial_mul_gamma C p 0 x

omit [CompleteSpace C] [IsAlgClosed C] in
private theorem gamma_one (x : A) : gamma C p 1 x = ι x := by
  simpa only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
    factorial_mul_gamma C p 1 x

private theorem quotient_gamma_of_two_le (n : ℕ) (hn : 2 ≤ n) (x : A)
    (hx : x ∈ RingHom.ker θ) : q (gamma C p n x) = 0 := by
  rw [fontaineKernel_eq_span C p, Ideal.mem_span_singleton] at hx
  obtain ⟨b, hb⟩ := hx
  have hξmk : q ((ι ξ) ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ((ι ξ) ^ 2))
  have hξ : (q (ι ξ)) ^ 2 = 0 := (map_pow (q) (ι ξ) 2).symm.trans hξmk
  have hx2 : (q (ι x)) ^ 2 = 0 := by
    rw [hb, map_mul ι, map_mul (q), mul_pow, hξ, zero_mul]
  simp only [gamma, map_mul (q), map_pow (q), pow_eq_zero_of_le hn hx2, mul_zero]

private def firstOrderMap : A0 C p →+* B ⧸ J :=
  (q).comp (A0 C p).val.toRingHom

private theorem firstOrderMap_mem_range (z : A0 C p) :
    firstOrderMap C p z ∈ ((q).comp ι).range := by
  change q z.1 ∈ ((q).comp ι).range
  refine Algebra.adjoin_induction (p := fun y _ => q y ∈ ((q).comp ι).range)
    ?_ ?_ ?_ ?_ z.2
  · rintro _ ⟨n, x, hx, rfl⟩
    cases n with
    | zero =>
      rw [gamma_zero, map_one]
      exact Subring.one_mem _
    | succ n =>
      cases n with
      | zero =>
        rw [gamma_one]
        exact RingHom.mem_range_self ((q).comp ι) x
      | succ n =>
        rw [quotient_gamma_of_two_le C p _ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) x hx]
        exact Subring.zero_mem _
  · exact RingHom.mem_range_self ((q).comp ι)
  · intro x y _ _ hx hy
    rw [map_add]
    exact Subring.add_mem _ hx hy
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subring.mul_mem _ hx hy

private theorem firstOrderMap_logPartialSum (x : A) (hx : x ∈ RingHom.ker θ) {N : ℕ}
    (hN : 0 < N) :
    firstOrderMap C p (DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C p n x (Ideal.mem_sup_left hx)) N) = q (ι x) := by
  let g := fun n => gammaInOfMemKerSupPrime C p n x (Ideal.mem_sup_left hx)
  have hmap (n : ℕ) : firstOrderMap C p (g n) = q (gamma C p n x) := rfl
  change firstOrderMap C p (DividedPowerLog.logPartialSum g N) = _
  rw [DividedPowerLog.logPartialSum, map_sum]
  calc
    _ = firstOrderMap C p (DividedPowerLog.logTerm g 0) := by
      apply Finset.sum_eq_single 0
      · intro n _ hn
        have hn' : 2 ≤ n + 1 := Nat.succ_le_succ (Nat.pos_of_ne_zero hn)
        rw [DividedPowerLog.logTerm, map_mul (firstOrderMap C p), hmap,
          quotient_gamma_of_two_le C p _ hn' x hx, mul_zero]
      · intro h
        exact (h (Finset.mem_range.mpr hN)).elim
    _ = _ := by
      simp only [DividedPowerLog.logTerm, pow_zero, Nat.factorial_zero, Nat.cast_one,
        one_mul, hmap, Nat.zero_add, gamma_one]

/-- Every nonempty partial sum differs from its linear term by a multiple of `ξ²`. -/
theorem logPartialSum_sub_algebraMap_dvd_primitive_sq (x : A) (hx : x ∈ RingHom.ker θ)
    {N : ℕ} (hN : 0 < N) :
    (ι ξ) ^ 2 ∣ ((DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C p n x (Ideal.mem_sup_left hx)) N : A0 C p) : B) - ι x := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  exact sub_eq_zero.mpr (firstOrderMap_logPartialSum C p x hx hN)

omit [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Fact p.Prime] in
private theorem prime_ne_zero_field : (p : C) ≠ 0 :=
  norm_pos_iff.mp (Fact.out : 0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1).1

private def thetaInField : A →+* C := (Subring.subtype 𝒪).comp θ

private theorem thetaInField_prime_isUnit : IsUnit (thetaInField C p (p : A)) := by
  rw [map_natCast]
  exact (prime_ne_zero_field C p).isUnit

/-- The Fontaine map on the Witt ring with `p` inverted. -/
def thetaAway : B →+* C :=
  Localization.awayLift (thetaInField C p) (p : A) (thetaInField_prime_isUnit C p)

theorem thetaAway_algebraMap (x : A) : thetaAway C p (ι x) = (θ x : C) :=
  IsLocalization.Away.lift_eq (p : A) (thetaInField_prime_isUnit C p) x

private theorem thetaAway_eq_zero {x : A} (hx : x ∈ RingHom.ker θ) :
    thetaAway C p (ι x) = 0 := by
  rw [thetaAway_algebraMap, RingHom.mem_ker.mp hx, Subring.coe_zero]

private theorem firstOrder_dvd_of_quotient_eq (x b : A) (hxb : x = ξ * b) (y : A)
    (m k : ℕ) (h : q (ι ((p : A) ^ m * x)) = q (ι ((p : A) ^ k * y))) :
    (p : 𝒪) ^ k ∣ (p : 𝒪) ^ m * θ b := by
  have hmem : ι ((p : A) ^ m * x) - ι ((p : A) ^ k * y) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, h, sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmem
  have hξI := fontainePrimitive_mem_ker C p
  have hξ := thetaAway_eq_zero C p hξI
  have hxI : x ∈ RingHom.ker θ := by
    rw [hxb]
    exact Ideal.mul_mem_right _ _ hξI
  have hx := thetaAway_eq_zero C p hxI
  have hyI : y ∈ RingHom.ker θ := by
    have hz := congrArg (thetaAway C p) hr
    simp only [map_sub, map_mul, map_pow, map_natCast, hξ, hx, zero_pow (by decide : 2 ≠ 0),
      zero_mul, mul_zero, zero_sub, neg_eq_zero] at hz
    have hy := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero k (prime_ne_zero_field C p))
    exact RingHom.mem_ker.mpr (Subtype.ext ((thetaAway_algebraMap C p y).symm.trans hy))
  rw [fontaineKernel_eq_span C p, Ideal.mem_span_singleton] at hyI
  obtain ⟨c, hc⟩ := hyI
  have hfactor : ι ξ * ((p : B) ^ m * ι b - (p : B) ^ k * ι c) = ι ξ * (ι ξ * r) := by
    calc
      _ = ι ((p : A) ^ m * x) - ι ((p : A) ^ k * y) := by
        simp only [hxb, hc, map_mul, map_pow, map_natCast]
        ring
      _ = _ := by rw [hr, pow_two, mul_assoc]
  have hξne : ι ξ ≠ 0 := by
    intro he
    apply fontainePrimitive_ne_zero C p
    exact algebraMap_injective C p (he.trans (map_zero ι).symm)
  have hz := congrArg (thetaAway C p) (mul_left_cancel₀ hξne hfactor)
  simp only [map_sub, map_mul, map_pow, map_natCast, hξ, zero_mul, thetaAway_algebraMap] at hz
  refine ⟨θ c, Subtype.ext ?_⟩
  simpa only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast] using sub_eq_zero.mp hz

/-- The first-order coordinate detects the given crystalline logarithm after inverting `p`. -/
theorem logOfMemKer_survives_of_firstOrder (x : A) (hx : x ∈ RingHom.ker θ)
    (b : A) (hxb : x = ξ * b) (hb : θ b ≠ 0) :
    algebraMap (ACris C p) (Localization.Away (p : ACris C p))
      (logOfMemKerSupPrime C p x (Ideal.mem_sup_left hx)) ≠ 0 := by
  intro hz
  let z := logOfMemKerSupPrime C p x (Ideal.mem_sup_left hx)
  obtain ⟨⟨_, ⟨m, rfl⟩⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : ACris C p))
      (Localization.Away (p : ACris C p)) z).mp hz
  change (p : ACris C p) ^ m * z = 0 at hm
  have hdiv (k : ℕ) : (p : 𝒪) ^ k ∣ (p : 𝒪) ^ m * θ b := by
    let N := p * k + 1
    let a := DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C p n x (Ideal.mem_sup_left hx)) N
    have hN : 0 < N := Nat.succ_pos _
    have ha : AdicCompletion.evalₐ I k z = Ideal.Quotient.mk (I ^ k) a :=
      eval_logOfMemKerSupPrime C p x (Ideal.mem_sup_left hx) (Nat.le_succ (p * k))
    have hv := congrArg (AdicCompletion.evalₐ I k) hm
    rw [map_mul, map_pow, ha, map_zero] at hv
    have hk : Ideal.Quotient.mk (I ^ k) ((p : A0 C p) ^ m * a) = 0 := by
      simpa only [map_mul, map_pow, map_natCast] using hv
    have hka := Ideal.Quotient.eq_zero_iff_mem.mp hk
    rw [Ideal.span_singleton_pow] at hka
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hka
    obtain ⟨y, hy⟩ := RingHom.mem_range.mp (firstOrderMap_mem_range C p t)
    change q (ι y) = firstOrderMap C p t at hy
    have hq : firstOrderMap C p a = q (ι x) := firstOrderMap_logPartialSum C p x hx hN
    have h := congrArg (firstOrderMap C p) ht
    simp only [map_mul, map_pow, map_natCast, hq, ← hy] at h
    apply firstOrder_dvd_of_quotient_eq C p x b hxb y m k
    simpa only [map_mul, map_pow, map_natCast] using h
  have hout : (p : 𝒪) ^ m * θ b = 0 := by
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : 𝒪)}) 𝒪)
    intro k
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr (hdiv k)
  have hp : (p : 𝒪) ≠ 0 := by
    intro h
    exact prime_ne_zero_field C p (congrArg (fun x : 𝒪 => (x : C)) h)
  exact hb ((mul_eq_zero.mp hout).resolve_left (pow_ne_zero _ hp))

variable [CharZero C]

/-- The actual crystalline logarithm of the original Tate-basis generator survives in `A_cris[1/p]`. -/
theorem cyclotomicLog_tateBasisGenerator_survives :
    algebraMap (ACris C p) (Localization.Away (p : ACris C p))
      (cyclotomicLog C p (LocalKummer.TateBasis.generator (p := p) (Ω := C))) ≠ 0 := by
  obtain ⟨b, hb, hxb⟩ := tateBasisGenerator_exists_firstOrder C p
  exact logOfMemKer_survives_of_firstOrder C p _
    (LocalKummer.RootTower.cyclotomic_teichmuller_sub_one_mem_theta_ker _) b hxb hb

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
