import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltSharp
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRootTower

/-!
source-id: JT-SCENE1-CYCLOTOMIC-TATE-TILT
source: Joshi II eq:tate-module-of-lubin-tate (935--938), allowing the
multiplicative formal group, and pr:teichmuller-lift-A (940--958).
fidelity: uses the original compatible roots of unity, not newly selected
roots. Recovers every coordinate by inverse Frobenius and untilting, and
identifies the actual cyclotomic inverse limit with the sharp-one fiber.
The additive logarithmic period in B^{phi=p} is a separate obligation.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.CyclotomicTateTilt

noncomputable section
universe u
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω] [CompleteSpace Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

private abbrev O := LocalGeometricFontaine.integerRing Ω
private abbrev Source := GeometricTiltField.Source Ω p
private abbrev Tate := LocalKummer.cyclotomicTateGroup p Ω

/-- Each actual torsion coordinate belongs to the original valuation integers. -/
def coordinate (x : Tate Ω p) (n : ℕ) : O Ω :=
  ⟨(x.1 n : Ω), (LocalGeometricFontaine.mem_integerRing Ω _).mpr (by
    have hpow : (x.1 n : Ω) ^ (p ^ n) = 1 := by
      exact congrArg (fun z : Ωˣ => (z : Ω)) (x.2.1 n)
    have hn : ‖(x.1 n : Ω)‖ ^ (p ^ n) = 1 := by
      rw [← norm_pow, hpow, norm_one]
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _)
      (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp hn.le)⟩

omit hp [CompleteSpace Ω] in
theorem coordinate_zero (x : Tate Ω p) : coordinate Ω p x 0 = 1 := by
  apply Subtype.ext
  change (x.1 0 : Ω) = 1
  have h := congrArg (fun z : Ωˣ => (z : Ω)) (x.2.1 0)
  simpa only [pow_zero, pow_one, Units.val_one] using h

omit hp [CompleteSpace Ω] in
theorem coordinate_succ (x : Tate Ω p) (n : ℕ) :
    coordinate Ω p x (n + 1) ^ p = coordinate Ω p x n := by
  apply Subtype.ext
  exact congrArg (fun z : Ωˣ => (z : Ω)) (x.2.2 n)

omit hp [CompleteSpace Ω] in
theorem coordinate_pow (x : Tate Ω p) (n m : ℕ) :
    coordinate Ω p x (n + m) ^ (p ^ m) = coordinate Ω p x n := by
  induction m with
  | zero => simp only [Nat.add_zero, pow_zero, pow_one]
  | succ m ih =>
      rw [Nat.add_succ, pow_succ', pow_mul, coordinate_succ, ih]

omit hp [CompleteSpace Ω] in
theorem coordinate_one (n : ℕ) : coordinate Ω p 1 n = 1 := rfl

omit hp [CompleteSpace Ω] in
theorem coordinate_mul (x y : Tate Ω p) (n : ℕ) :
    coordinate Ω p (x * y) n = coordinate Ω p x n * coordinate Ω p y n := rfl

/-- Reduction of the original compatible roots, as a multiplicative map. -/
def toPreTilt : Tate Ω p →* Source Ω p where
  toFun x := ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : O Ω)}) (coordinate Ω p x n),
    fun n => by
      rw [← map_pow, coordinate_succ]⟩
  map_one' := by
    apply Perfection.ext
    intro n
    change Ideal.Quotient.mk _ (coordinate Ω p 1 n) = 1
    rw [coordinate_one, map_one]
  map_mul' x y := by
    apply Perfection.ext
    intro n
    change Ideal.Quotient.mk _ (coordinate Ω p (x * y) n) =
      Ideal.Quotient.mk _ (coordinate Ω p x n) *
        Ideal.Quotient.mk _ (coordinate Ω p y n)
    rw [coordinate_mul, map_mul]

/-- Untilting an inverse-Frobenius shift recovers the original root exactly. -/
theorem untilt_shift_toPreTilt (x : Tate Ω p) (n : ℕ) :
    PreTilt.untilt (((frobeniusEquiv (Source Ω p) p).symm^[n]) (toPreTilt Ω p x)) =
      coordinate Ω p x n := by
  change Perfection.teichmuller p (Ideal.span {(p : O Ω)}) _ = _
  apply Perfection.teichmuller_spec
  intro m
  refine ⟨coordinate Ω p x (m + n), ?_, ?_⟩
  · change Ideal.Quotient.mk _ (coordinate Ω p x (m + n)) =
      PreTilt.coeff m (((frobeniusEquiv (Source Ω p) p).symm^[n]) (toPreTilt Ω p x))
    rw [PreTilt.coeff_iterate_frobeniusEquiv_symm]
    rfl
  · rw [Nat.add_comm m n, coordinate_pow]
    simp only [SModEq.refl]

theorem untilt_toPreTilt (x : Tate Ω p) :
    PreTilt.untilt (toPreTilt Ω p x) = 1 := by
  simpa only [Function.iterate_zero_apply, coordinate_zero] using
    untilt_shift_toPreTilt Ω p x 0

theorem sharp_toPreTilt (x : Tate Ω p) :
    GeometricTiltSharp.integralSharp Ω p (toPreTilt Ω p x) = 1 := by
  change ((PreTilt.untilt (toPreTilt Ω p x) : O Ω) : Ω) = 1
  rw [untilt_toPreTilt, OneMemClass.coe_one]

theorem toPreTilt_injective : Function.Injective (toPreTilt Ω p) := by
  intro x y h
  apply Subtype.ext
  funext n
  apply Units.ext
  have hn := congrArg (fun a : Source Ω p =>
    PreTilt.untilt (((frobeniusEquiv (Source Ω p) p).symm^[n]) a)) h
  rw [untilt_shift_toPreTilt, untilt_shift_toPreTilt] at hn
  exact congrArg Subtype.val hn

/-- The fiber uses the existing multiplicative sharp; it has no additive structure here. -/
def sharpOne : Submonoid (Source Ω p) where
  carrier := {a | GeometricTiltSharp.integralSharp Ω p a = 1}
  one_mem' := map_one _
  mul_mem' {a b} ha hb := by
    change GeometricTiltSharp.integralSharp Ω p (a * b) = 1
    change GeometricTiltSharp.integralSharp Ω p a = 1 at ha
    change GeometricTiltSharp.integralSharp Ω p b = 1 at hb
    rw [map_mul, ha, hb, one_mul]

def toSharpOne : Tate Ω p →* sharpOne Ω p where
  toFun x := ⟨toPreTilt Ω p x, sharp_toPreTilt Ω p x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)

private def shift (a : Source Ω p) (n : ℕ) : O Ω :=
  PreTilt.untilt (((frobeniusEquiv (Source Ω p) p).symm^[n]) a)

private theorem shift_succ (a : Source Ω p) (n : ℕ) :
    shift Ω p a (n + 1) ^ p = shift Ω p a n := by
  unfold shift
  rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

private theorem shift_pow (a : sharpOne Ω p) (n : ℕ) :
    (shift Ω p a.1 n : Ω) ^ (p ^ n) = 1 := by
  have h := congrArg (fun z : O Ω => (z : Ω))
    (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow a.1 n)
  exact h.trans a.2

/-- Sharp-one elements supply the actual compatible roots of unity in the untilt. -/
def fromSharpOne (a : sharpOne Ω p) : Tate Ω p :=
  ⟨fun n => Units.mk0 (shift Ω p a.1 n : Ω) (by
    intro hz
    have h := shift_pow Ω p a n
    rw [hz, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at h
    exact zero_ne_one h), by
    constructor
    · intro n
      apply Units.ext
      exact shift_pow Ω p a n
    · intro n
      apply Units.ext
      exact congrArg (fun z : O Ω => (z : Ω)) (shift_succ Ω p a.1 n)⟩

/-- Exact multiplicative identification, with both inverses proved on the original carriers. -/
def sharpOneEquiv : Tate Ω p ≃* sharpOne Ω p where
  toFun := toSharpOne Ω p
  invFun := fromSharpOne Ω p
  left_inv x := by
    apply Subtype.ext
    funext n
    apply Units.ext
    exact congrArg (fun z : O Ω => (z : Ω)) (untilt_shift_toPreTilt Ω p x n)
  right_inv a := by
    apply Subtype.ext
    apply Perfection.ext
    intro n
    change Ideal.Quotient.mk (Ideal.span {(p : O Ω)}) (shift Ω p a.1 n) =
      PreTilt.coeff n a.1
    rw [shift, PreTilt.mk_untilt_eq_coeff_zero,
      PreTilt.coeff_iterate_frobeniusEquiv_symm, Nat.zero_add]
  map_mul' x y := map_mul (toSharpOne Ω p) x y

end
end JoshiTeich.Act1Scene1.CyclotomicTateTilt
