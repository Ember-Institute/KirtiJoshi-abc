import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateExactSequence
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaBound
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitNegation

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-ONE-UNIT-BALL
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`;
`B^+` is defined by the Fargues--Fontaine `rho=1` unit-ball condition
(`pr:teichmuller-lift-A`, 1051--1076, citing FF Proposition 1.10.7).
fidelity: in the original actual bounded Witt localization, proves that
the rho=1 unit ball consists exactly of elements with an integral Ainf
numerator and a p-power denominator. A primitive-factor denominator is
removed coefficient by coefficient using the actual tilt valuation.
This constructs the p-local source witness; the rho=1 norm is the actual
weighted Teichmuller coefficient value. Original proofs; no reference
implementation copied.
boundary: Scene1/Derived; this is a concrete unit-ball description for
the actual carrier, not an identification with the paper's full Frechet
ring or a global holomorphoid. The other rho norms and paper B identity
remain separate. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoOneUnitBall

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion
open InitialThetaBoundedWittLocalization InitialThetaWittRhoNorm
open InitialThetaTiltFontaine WittTeichmullerExpansion
open scoped ENNReal
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def HasPIntegralPresentation (x : Ring D w) : Prop :=
  ∃ n : ℕ, ∃ a : Ainf D w,
    x * (Arithmetic.residueChar w.1 : Ring D w) ^ n = inclusion D w a

private theorem realValue_mul_prime_one (x : Ring D w) :
    realValue D w 1 (x * (Arithmetic.residueChar w.1 : Ring D w)) = realValue D w 1 x := by
  change (InitialThetaWittRhoValue.value D w 1 (x * Arithmetic.residueChar w.1)).toReal = _
  rw [InitialThetaWittRhoValue.value_mul_prime D w 1 (by norm_num) ENNReal.one_ne_top]
  simp [realValue]

private theorem realValue_mul_prime_pow_one (x : Ring D w) (n : ℕ) :
    realValue D w 1 (x * (Arithmetic.residueChar w.1 : Ring D w) ^ n) = realValue D w 1 x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      realValue D w 1 (x * (Arithmetic.residueChar w.1 : Ring D w) ^ (n + 1)) =
          realValue D w 1 ((x * (Arithmetic.residueChar w.1 : Ring D w) ^ n) *
            (Arithmetic.residueChar w.1 : Ring D w)) := by rw [pow_succ]; ac_rfl
      _ = realValue D w 1 (x * (Arithmetic.residueChar w.1 : Ring D w) ^ n) :=
        realValue_mul_prime_one D w _
      _ = realValue D w 1 x := ih

private theorem realValue_pow_le (x : Ring D w) (n : ℕ) :
    realValue D w 1 (x ^ n) ≤ realValue D w 1 x ^ n := by
  induction n with
  | zero => simp [realValue_one]
  | succ n ih =>
    rw [pow_succ]
    exact (realValue_mul_le D w 1 (by norm_num) (by norm_num) _ _).trans
      (mul_le_mul_of_nonneg_right ih (realValue_nonneg D w 1 x))

private theorem realValue_inclusion_le_one (a : Ainf D w) :
    realValue D w 1 (inclusion D w a) ≤ 1 := by
  rw [realValue, InitialThetaWittRhoValue.value_inclusion D w 1 (by norm_num) ENNReal.one_ne_top]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    (WittWeightedDigitNegation.value_map_le_one (Arithmetic.residueChar w.1)
      (LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w))
      (LocalGeometricFontaine.mem_integerRing (InitialThetaTiltField.Carrier D w))
      1 (by norm_num) a)

private theorem realValue_denominator_le_varpi :
    realValue D w 1 (inclusion D w (denominator D w)) ≤ ‖(varpi D w : InitialThetaTiltField.Carrier D w)‖ := by
  rw [realValue, InitialThetaWittRhoValue.value_inclusion D w 1 (by norm_num) ENNReal.one_ne_top]
  change (WittWeightedDigits.value (Arithmetic.residueChar w.1) 1
    (wittInclusion D w (denominator D w))).toReal ≤ _
  rw [denominator, wittInclusion, map_mul, map_natCast, teichVarpi,
    WittVector.map_teichmuller]
  have hm := WittWeightedDigitMultiplication.value_mul_le (Arithmetic.residueChar w.1)
    (LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w))
    (LocalGeometricFontaine.mem_integerRing (InitialThetaTiltField.Carrier D w))
    1 (by norm_num)
    (Arithmetic.residueChar w.1 : WittVector (Arithmetic.residueChar w.1)
      (InitialThetaTiltField.Carrier D w))
    (WittVector.teichmuller (Arithmetic.residueChar w.1)
      (varpi D w : InitialThetaTiltField.Carrier D w))
  have hval : WittWeightedDigits.value (Arithmetic.residueChar w.1) 1
      ((Arithmetic.residueChar w.1 : WittVector (Arithmetic.residueChar w.1)
        (InitialThetaTiltField.Carrier D w)) *
        WittVector.teichmuller (Arithmetic.residueChar w.1)
          (varpi D w : InitialThetaTiltField.Carrier D w)) ≤
      ENNReal.ofReal ‖(varpi D w : InitialThetaTiltField.Carrier D w)‖ := by
    calc
      _ ≤ WittWeightedDigits.value (Arithmetic.residueChar w.1) 1
          (Arithmetic.residueChar w.1 : WittVector (Arithmetic.residueChar w.1)
            (InitialThetaTiltField.Carrier D w)) *
          WittWeightedDigits.value (Arithmetic.residueChar w.1) 1
            (WittVector.teichmuller (Arithmetic.residueChar w.1)
              (varpi D w : InitialThetaTiltField.Carrier D w)) := hm
      _ = _ := by rw [WittWeightedDigits.value_prime, WittWeightedDigits.value_teichmuller]; simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hval).trans_eq
    (ENNReal.toReal_ofReal (norm_nonneg _))

theorem unitBallAtOne_iff_hasPIntegralPresentation (x : Ring D w) :
    realValue D w 1 x ≤ 1 ↔ HasPIntegralPresentation D w x := by
  constructor
  · intro hx
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (denominator D w) x
    have hden : realValue D w 1 (inclusion D w (denominator D w)) ^ n ≤
        ‖(varpi D w : InitialThetaTiltField.Carrier D w)‖ ^ n :=
      pow_le_pow_left₀ (realValue_nonneg D w 1 _) (realValue_denominator_le_varpi D w) _
    have haNorm : realValue D w 1 (inclusion D w a) ≤
        ‖(varpi D w : InitialThetaTiltField.Carrier D w)‖ ^ n := by
      calc
        realValue D w 1 (inclusion D w a) =
            realValue D w 1 (x * inclusion D w (denominator D w) ^ n) :=
          (congrArg (realValue D w 1) ha).symm
        _ ≤ realValue D w 1 x * realValue D w 1 (inclusion D w (denominator D w) ^ n) :=
          realValue_mul_le D w 1 (by norm_num) (by norm_num) _ _
        _ ≤ 1 * realValue D w 1 (inclusion D w (denominator D w) ^ n) :=
          mul_le_mul_of_nonneg_right hx (realValue_nonneg D w 1 _)
        _ = realValue D w 1 (inclusion D w (denominator D w) ^ n) := one_mul _
        _ ≤ realValue D w 1 (inclusion D w (denominator D w)) ^ n :=
          realValue_pow_le D w _ n
        _ ≤ ‖(varpi D w : InitialThetaTiltField.Carrier D w)‖ ^ n := hden
    have hdigits (i : ℕ) :
        ‖digits (Arithmetic.residueChar w.1) (wittInclusion D w a) i‖ ≤
          ‖(varpi D w : InitialThetaTiltField.Carrier D w)‖ ^ n := by
      have ht := WittWeightedDigits.term_le_value (Arithmetic.residueChar w.1) 1
        (wittInclusion D w a) i
      have hfin := InitialThetaWittRhoValue.value_lt_top D w 1 (by norm_num)
        (by norm_num : (1 : ℝ≥0∞) ≤ 1) (inclusion D w a)
      simp only [one_pow, mul_one] at ht
      have heq : InitialThetaWittRhoValue.value D w 1 (inclusion D w a) =
          ENNReal.ofReal (realValue D w 1 (inclusion D w a)) :=
        (ENNReal.ofReal_toReal hfin.ne).symm
      rw [← InitialThetaWittRhoValue.value_inclusion D w 1 (by norm_num)
        ENNReal.one_ne_top a] at ht
      rw [heq] at ht
      have := ht.trans (ENNReal.ofReal_le_ofReal haNorm)
      exact (ENNReal.ofReal_le_ofReal_iff
        (pow_nonneg (norm_nonneg (varpi D w : InitialThetaTiltField.Carrier D w)) n)).mp this
    let v : InitialThetaTiltField.Carrier D w := varpi D w
    let c : ℕ → InitialThetaTiltField.Carrier D w := fun i =>
      digits (Arithmetic.residueChar w.1) (wittInclusion D w a) i
    have hv : v ≠ 0 := norm_pos_iff.mp (varpi_norm_pos_lt_one D w).1
    have hscaled (i : ℕ) : ‖c i / v ^ n‖ ≤ 1 := by
      rw [norm_div, norm_pow]
      exact (div_le_one_of_le₀ (hdigits i) (pow_nonneg (norm_nonneg v) n))
    let e : ℕ → InitialThetaTiltIntegers.Integers D w := fun i =>
      ⟨c i / v ^ n, (LocalGeometricFontaine.mem_integerRing _ _).mpr (hscaled i)⟩
    let b : Ainf D w := WittVector.mk (Arithmetic.residueChar w.1)
      (fun i => e i ^ (Arithmetic.residueChar w.1 ^ i))
    have hbexp : Expands (Arithmetic.residueChar w.1)
        (wittInclusion D w b) (fun i => c i / v ^ n) := by
      apply (expands_iff_coeff _ _ _).mpr
      intro i
      change (c i / v ^ n) ^ (Arithmetic.residueChar w.1 ^ i) = _
      rfl
    have hteichPow : WittVector.teichmuller (Arithmetic.residueChar w.1) (v ^ n) =
        WittVector.teichmuller (Arithmetic.residueChar w.1) v ^ n :=
      map_pow (WittVector.teichmuller (Arithmetic.residueChar w.1)) v n
    have hteich : WittVector.teichmuller (Arithmetic.residueChar w.1) v ^ n *
        wittInclusion D w b = wittInclusion D w a := by
      have hcancelDigits (i : ℕ) : v ^ n * (c i / v ^ n) = c i := by
        rw [div_eq_mul_inv]
        calc
          _ = c i * (v ^ n * (v ^ n)⁻¹) := by ac_rfl
          _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero n hv), mul_one]
      have hmulExp : Expands (Arithmetic.residueChar w.1)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) v ^ n * wittInclusion D w b) c := by
        simpa only [← hteichPow, hcancelDigits] using
          (expands_teichmuller_mul (Arithmetic.residueChar w.1) (v ^ n)
            (wittInclusion D w b) _ hbexp)
      exact expansion_unique (Arithmetic.residueChar w.1)
        (WittVector.teichmuller (Arithmetic.residueChar w.1) v ^ n * wittInclusion D w b)
        (wittInclusion D w a) c hmulExp
        (expands_digits (Arithmetic.residueChar w.1) (wittInclusion D w a))
    have haEq : a = teichVarpi D w ^ n * b := by
      apply wittInclusion_injective D w
      change wittInclusion D w a =
        WittVector.map _ (teichVarpi D w ^ n * b)
      rw [map_mul, map_pow, teichVarpi, WittVector.map_teichmuller]
      exact hteich.symm
    have hcancel : x * inclusion D w (Arithmetic.residueChar w.1) ^ n = inclusion D w b := by
      apply mul_right_cancel₀ ((teichVarpi_isUnit D w).pow n).ne_zero
      calc
        (x * inclusion D w (Arithmetic.residueChar w.1) ^ n) * inclusion D w (teichVarpi D w) ^ n =
            inclusion D w a := by
              have hd : inclusion D w (Arithmetic.residueChar w.1) ^ n *
                  inclusion D w (teichVarpi D w) ^ n =
                    inclusion D w (denominator D w) ^ n := by
                  change inclusion D w (Arithmetic.residueChar w.1) ^ n *
                    inclusion D w (teichVarpi D w) ^ n =
                      inclusion D w ((Arithmetic.residueChar w.1 : Ainf D w) * teichVarpi D w) ^ n
                  rw [← map_pow, ← map_pow, ← map_mul]
                  simpa only [map_mul, map_pow] using
                    congrArg (inclusion D w)
                      ((mul_pow (Arithmetic.residueChar w.1 : Ainf D w)
                        (teichVarpi D w) n).symm)
              calc
                _ = x * inclusion D w (denominator D w) ^ n := by rw [← hd]; ac_rfl
                _ = _ := ha
        _ = inclusion D w b * inclusion D w (teichVarpi D w) ^ n := by
          rw [haEq, map_mul, map_pow, mul_comm]
    exact ⟨n, b, by simpa only [map_natCast] using hcancel⟩
  · rintro ⟨n, a, ha⟩
    have he := congrArg (realValue D w 1) ha
    rw [realValue_mul_prime_pow_one D w x n] at he
    exact he.le.trans (realValue_inclusion_le_one D w a)

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoOneUnitBall
