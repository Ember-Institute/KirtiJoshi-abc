import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittExponentialLinearization

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EXPONENTIAL-CONTRACTION
source: Joshi II `pr:teichmuller-lift-A`, multiplicative-formal-group
periods; the actual exponential addition law and its quadratic remainder.
fidelity: on the concrete closed ball of radius rho^2/2 in the original
rho completion, exp(x)-1-x is Lipschitz with constant one half. Uses
the original ring, norm and convergent series, without an inverse law.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no local surjectivity, Teichmuller recognition
or full period representation is input. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittExponentialContraction

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittExponentialSeries InitialThetaWittExponentialMultiplication
open InitialThetaWittExponentialLinearization
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def smallRadius (ρ : Radius) : ℝ := ρ.val.toReal ^ 2 / 2

theorem smallRadius_pos (ρ : Radius) : 0 < smallRadius ρ :=
  div_pos (pow_pos (radius_toReal_pos ρ) 2) (by norm_num)

theorem smallRadius_lt_radius (ρ : Radius) : smallRadius ρ < ρ.val.toReal := by
  have h := mul_lt_mul_of_pos_left (radius_toReal_lt_one ρ) (radius_toReal_pos ρ)
  dsimp only [smallRadius]
  nlinarith [radius_toReal_pos ρ]

theorem smallRadius_lt_one (ρ : Radius) : smallRadius ρ < 1 :=
  (smallRadius_lt_radius ρ).trans (radius_toReal_lt_one ρ)

theorem ratio_le_half (ρ : Radius) (t : ℝ) (ht : t ≤ smallRadius ρ) : t / ρ.val.toReal ≤ 1 / 2 := by
  apply (div_le_iff₀ (radius_toReal_pos ρ)).mpr
  have h := mul_lt_mul_of_pos_left (radius_toReal_lt_one ρ) (radius_toReal_pos ρ)
  dsimp only [smallRadius] at ht
  nlinarith

theorem quadratic_le_half_mul (ρ : Radius) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ smallRadius ρ) :
    (t / ρ.val.toReal) ^ 2 ≤ (1 / 2 : ℝ) * t := by
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (radius_toReal_pos ρ) 2)).mpr
  have h := mul_le_mul_of_nonneg_right ht ht0
  dsimp only [smallRadius] at h
  nlinarith

def remainder (ρ : Radius) (x : Ring D w ρ) : Ring D w ρ := exp D w ρ x - 1 - x

theorem remainder_zero (ρ : Radius) : remainder D w ρ 0 = 0 := by
  rw [remainder, exp_zero, sub_self, sub_zero]

theorem norm_exp_le_one (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ < ρ.val.toReal) :
    ‖exp D w ρ x‖ ≤ 1 := by
  calc
    _ = ‖(exp D w ρ x - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ max ‖exp D w ρ x - 1‖ ‖(1 : Ring D w ρ)‖ :=
      InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _
    _ ≤ 1 := max_le (norm_exp_sub_one_lt_one D w ρ x hx).le (by rw [norm_one])

theorem norm_sub_le_smallRadius (ρ : Radius) (a b : Ring D w ρ)
    (ha : ‖a‖ ≤ smallRadius ρ) (hb : ‖b‖ ≤ smallRadius ρ) : ‖a - b‖ ≤ smallRadius ρ := by
  have h := InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ a (-b)
  simp only [← sub_eq_add_neg, norm_neg] at h
  exact h.trans (max_le ha hb)

theorem remainder_sub (ρ : Radius) (a b : Ring D w ρ)
    (ha : ‖a‖ ≤ smallRadius ρ) (hb : ‖b‖ ≤ smallRadius ρ) :
    remainder D w ρ a - remainder D w ρ b =
      (exp D w ρ b - 1) * (a - b) + exp D w ρ b * remainder D w ρ (a - b) := by
  have hd := (norm_sub_le_smallRadius D w ρ a b ha hb).trans_lt (smallRadius_lt_radius ρ)
  have he : exp D w ρ a = exp D w ρ b * exp D w ρ (a - b) := by
    rw [← exp_add D w ρ b (a - b) (hb.trans_lt (smallRadius_lt_radius ρ)) hd]
    congr 1
    ring
  simp only [remainder]
  rw [he]
  ring

theorem norm_remainder_sub_le (ρ : Radius) (a b : Ring D w ρ)
    (ha : ‖a‖ ≤ smallRadius ρ) (hb : ‖b‖ ≤ smallRadius ρ) :
    ‖remainder D w ρ a - remainder D w ρ b‖ ≤ (1 / 2 : ℝ) * ‖a - b‖ := by
  have hb' := hb.trans_lt (smallRadius_lt_radius ρ)
  have hd := norm_sub_le_smallRadius D w ρ a b ha hb
  rw [remainder_sub D w ρ a b ha hb]
  apply (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _).trans
  apply max_le
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_exp_sub_one_le D w ρ b hb').trans (ratio_le_half ρ ‖b‖ hb)) (norm_nonneg _))
  · calc
      _ ≤ ‖remainder D w ρ (a - b)‖ :=
        (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_exp_le_one D w ρ b hb'))
      _ ≤ (‖a - b‖ / ρ.val.toReal) ^ 2 :=
        norm_exp_remainder_le D w ρ (a - b) (hd.trans_lt (smallRadius_lt_radius ρ))
      _ ≤ _ := quadratic_le_half_mul ρ ‖a - b‖ (norm_nonneg _) hd

theorem norm_remainder_le (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ ≤ smallRadius ρ) :
    ‖remainder D w ρ x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
  simpa only [remainder_zero, sub_zero] using norm_remainder_sub_le D w ρ x 0 hx
    (by simpa only [norm_zero] using (smallRadius_pos ρ).le)

theorem norm_exp_sub_one_le_norm (ρ : Radius) (x : Ring D w ρ) (hx : ‖x‖ ≤ smallRadius ρ) :
    ‖exp D w ρ x - 1‖ ≤ ‖x‖ := by
  have he : exp D w ρ x - 1 = x + remainder D w ρ x := by unfold remainder; ring
  rw [he]
  apply (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _).trans
  exact max_le le_rfl ((norm_remainder_le D w ρ x hx).trans (by nlinarith [norm_nonneg x]))

end
end JoshiTeich.Act1Scene1.InitialThetaWittExponentialContraction
