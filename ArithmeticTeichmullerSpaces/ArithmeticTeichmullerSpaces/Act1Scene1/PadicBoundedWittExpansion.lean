import ArithmeticTeichmullerSpaces.Act1Scene1.PadicBoundedWittLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigits
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.Localization.FractionRing

/-!
source-id: JT-SCENE1-STANDARD-PADIC-BOUNDED-WITT-EXPANSION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`.
fidelity: embeds the standard bounded Witt localization in Frac(W(F)).
Each element has a p-power denominator and a numerator with bounded
Teichmuller digits in the original standard tilt norm. Its weighted value
is finite at every radius at most one. All declarations depend only on p.
Original proofs; no reference implementation copied.
boundary: rho completion and identification with the completed paper B
remain open. Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicBoundedWittExpansion

open PadicBoundedWittLocalization WittTeichmullerExpansion
open scoped ENNReal
noncomputable section
variable (p : ℕ) [Fact p.Prime]

local instance coefficientField : Field (PadicTiltField.Carrier p) :=
  (PadicTiltField.carrierNormedField p).toField

local instance integersPerfect : PerfectRing (PadicTiltField.Integers p) p := by
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius
    (R := PadicTiltField.Carrier p) (p := p)).surjective (x : PadicTiltField.Carrier p)
  change y ^ p = (x : PadicTiltField.Carrier p) at hy
  have hnorm : ‖y‖ ^ p ≤ 1 := by
    rw [← norm_pow, hy]
    exact (LocalGeometricFontaine.mem_integerRing _ _).mp x.property
  let z : PadicTiltField.Integers p := ⟨y,
    (LocalGeometricFontaine.mem_integerRing _ _).mpr
      ((pow_le_one_iff_of_nonneg (norm_nonneg y) (Fact.out : p.Prime).ne_zero).mp hnorm)⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change (y : PadicTiltField.Carrier p) ^ p = (x : PadicTiltField.Carrier p)
  exact hy

abbrev FieldWitt := WittVector p (PadicTiltField.Carrier p)
abbrev Ambient := FractionRing (FieldWitt p)

def wittInclusion : Ainf p →+* FieldWitt p :=
  WittVector.map (algebraMap (PadicTiltField.Integers p) (PadicTiltField.Carrier p))

theorem wittInclusion_injective : Function.Injective (wittInclusion p) :=
  WittVector.map_injective _ (show Function.Injective
    (algebraMap (PadicTiltField.Integers p) (PadicTiltField.Carrier p)) from
      Subtype.val_injective)

def ambientInclusion : Ainf p →+* Ambient p :=
  (algebraMap (FieldWitt p) (Ambient p)).comp (wittInclusion p)

theorem ambientInclusion_injective : Function.Injective (ambientInclusion p) :=
  (IsFractionRing.injective (FieldWitt p) (Ambient p)).comp (wittInclusion_injective p)

def toAmbient : PadicBoundedWittLocalization.Ring p →+* Ambient p :=
  IsLocalization.Away.lift (denominator p) (g := ambientInclusion p) (by
    apply isUnit_iff_ne_zero.mpr
    have ht : wittInclusion p (teich p) ≠ 0 := by
      intro h
      have hc := congrArg (fun b : FieldWitt p => b.coeff 0) h
      have hz : (contraction p : PadicTiltField.Carrier p) = 0 := by
        have hc' : algebraMap (PadicTiltField.Integers p) (PadicTiltField.Carrier p)
            (contraction p) = 0 := by
          simpa only [wittInclusion, teich, WittVector.map_teichmuller,
            WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] using hc
        have hmap : algebraMap (PadicTiltField.Integers p) (PadicTiltField.Carrier p)
            (contraction p) = (contraction p : PadicTiltField.Carrier p) := rfl
        rw [hmap] at hc'
        exact hc'
      exact contraction_ne_zero p (Subtype.ext hz)
    have hd : wittInclusion p (denominator p) ≠ 0 := by
      rw [denominator, map_mul, map_natCast]
      exact mul_ne_zero (WittVector.p_nonzero p _) ht
    exact fun h => hd (IsFractionRing.injective (FieldWitt p) (Ambient p)
      (h.trans (map_zero _).symm)))

theorem toAmbient_inclusion (a : Ainf p) :
    toAmbient p (inclusion p a) = ambientInclusion p a :=
  IsLocalization.Away.lift_eq _ _ a

theorem toAmbient_injective : Function.Injective (toAmbient p) := by
  apply (injective_iff_map_eq_zero (toAmbient p)).mpr
  intro x hx
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (denominator p) x
  have ha0 : a = 0 := by
    apply ambientInclusion_injective p
    rw [map_zero, ← toAmbient_inclusion]
    change toAmbient p (algebraMap (Ainf p) (PadicBoundedWittLocalization.Ring p) a) = 0
    rw [← ha, map_mul, hx, zero_mul]
  rw [ha0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (denominator p)
    (S := PadicBoundedWittLocalization.Ring p)).pow n).mul_left_eq_zero.mp ha

private theorem exists_bounded_presentation (x : PadicBoundedWittLocalization.Ring p) :
    ∃ m : ℕ, ∃ y : FieldWitt p, ∃ C : ℝ,
      (∀ n : ℕ, ‖digits p y n‖ ≤ C) ∧
      toAmbient p x * (p : Ambient p) ^ m = algebraMap (FieldWitt p) (Ambient p) y := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (denominator p) x
  let v : PadicTiltField.Carrier p := contraction p
  have hv : v ≠ 0 := Subtype.coe_ne_coe.mpr (contraction_ne_zero p)
  let r := (v ^ m)⁻¹
  let d : ℕ → PadicTiltField.Integers p := digits p a
  let c : ℕ → PadicTiltField.Carrier p := fun n => r * (d n : PadicTiltField.Carrier p)
  let y : FieldWitt p := WittVector.teichmuller p r * wittInclusion p a
  refine ⟨m, y, ‖r‖, ?_, ?_⟩
  · have he : Expands p y c :=
      expands_teichmuller_mul p r _ _
        (expands_map p
          (algebraMap (PadicTiltField.Integers p) (PadicTiltField.Carrier p))
          a d (expands_digits p a))
    have hd : c = digits p y := digits_unique p y c he
    intro n
    rw [← hd]
    change ‖r * (d n : PadicTiltField.Carrier p)‖ ≤ ‖r‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      ((LocalGeometricFontaine.mem_integerRing _ _).mp (d n).property)
  · have he := congrArg (toAmbient p) ha
    have hden : ambientInclusion p (denominator p) =
        (p : Ambient p) * algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v) := by
      simp only [denominator, map_mul, map_natCast, ambientInclusion, RingHom.comp_apply,
        wittInclusion, teich, WittVector.map_teichmuller]
      rfl
    have hrel : toAmbient p x * ((p : Ambient p) *
        algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v)) ^ m =
        ambientInclusion p a := by
      simp only [map_mul, map_pow] at he
      change toAmbient p x * toAmbient p (inclusion p (denominator p)) ^ m =
        toAmbient p (inclusion p a) at he
      rwa [toAmbient_inclusion, toAmbient_inclusion, hden] at he
    have ht : WittVector.teichmuller p v ≠ 0 := by
      intro h
      have hc := congrArg (fun b : FieldWitt p => b.coeff 0) h
      exact hv (by simpa only [WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] using hc)
    have htImage : algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v) ≠ 0 := by
      intro h
      exact ht (IsFractionRing.injective (FieldWitt p) (Ambient p)
        (h.trans (map_zero _).symm))
    apply mul_right_cancel₀ (pow_ne_zero m htImage)
    calc
      (toAmbient p x * (p : Ambient p) ^ m) *
          algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v) ^ m =
          ambientInclusion p a := by
        rw [mul_assoc, ← mul_pow]
        exact hrel
      _ = algebraMap (FieldWitt p) (Ambient p) y *
          algebraMap (FieldWitt p) (Ambient p) (WittVector.teichmuller p v) ^ m := by
        change algebraMap (FieldWitt p) (Ambient p) (wittInclusion p a) = _
        rw [← map_pow, ← map_mul]
        congr 1
        change wittInclusion p a =
          (WittVector.teichmuller p r * wittInclusion p a) * WittVector.teichmuller p v ^ m
        rw [mul_right_comm, ← map_pow, ← map_mul]
        simp only [r, inv_mul_cancel₀ (pow_ne_zero m hv), map_one, one_mul]

theorem exists_presentation (x : PadicBoundedWittLocalization.Ring p) :
    ∃ m : ℕ, ∃ y : FieldWitt p,
      toAmbient p x * (p : Ambient p) ^ m = algebraMap (FieldWitt p) (Ambient p) y := by
  obtain ⟨m, y, C, hbound, hrel⟩ := exists_bounded_presentation p x
  exact ⟨m, y, hrel⟩

theorem toAmbient_exists_finite_value (ρ : ℝ≥0∞) (hρ1 : ρ ≤ 1)
    (x : PadicBoundedWittLocalization.Ring p) :
    ∃ m : ℕ, ∃ y : FieldWitt p,
      toAmbient p x * (p : Ambient p) ^ m = algebraMap (FieldWitt p) (Ambient p) y ∧
      WittWeightedDigits.value p ρ y < ⊤ := by
  obtain ⟨m, y, C, hbound, hrel⟩ := exists_bounded_presentation p x
  exact ⟨m, y, hrel, WittWeightedDigits.value_lt_top_of_bound p ρ hρ1 y C hbound⟩

end
end JoshiTeich.Act1Scene1.PadicBoundedWittExpansion
