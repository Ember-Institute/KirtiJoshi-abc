import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLocalizationChoice
import ArithmeticTeichmullerSpaces.Act1Scene1.WittTeichmullerExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-EXPANSION
source: Joshi II se:ff-rings / W(O_F) into B (511--512, 719--727);
Mathlib actual Witt/Teichmuller expansions and the tilt valuation integers.
fidelity: embeds the existing localization in Frac(W(F)), and identifies
its image with actual p-power-denominator Witt elements whose unique
Teichmuller digits are uniformly bounded in the original tilt norm.
Both directions are proved on existing carriers, without a free expansion
or boundedness certificate for the actual localization elements.
No rho norm or Frechet completion is asserted. Original proofs;
Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittExpansion

open JoshiTeich.Prologue InitialThetaTiltFontaine InitialThetaCanonicalGeometricFontaine
open InitialThetaBoundedWittLocalization
open WittTeichmullerExpansion
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

local instance coefficientField : Field (InitialThetaTiltField.Carrier D w) :=
  InitialThetaTiltField.carrierField D w

private def coefficientInclusion :
    InitialThetaTiltIntegers.Integers D w →+* InitialThetaTiltField.Carrier D w where
  toFun := Subtype.val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

abbrev FieldWitt := WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Carrier D w)
abbrev Ambient := FractionRing (FieldWitt D w)

def wittInclusion :=
  WittVector.map (p := Arithmetic.residueChar w.1)
    (coefficientInclusion D w)

theorem wittInclusion_coeff_norm (a : Ainf D w) (n : ℕ) :
    ‖(wittInclusion D w a).coeff n‖ = ‖a.coeff n‖ := rfl

theorem wittInclusion_injective : Function.Injective (wittInclusion D w) :=
  WittVector.map_injective _ (show Function.Injective
    (coefficientInclusion D w) from
      Subtype.val_injective)

def ambientInclusion : Ainf D w →+* Ambient D w :=
  (algebraMap (FieldWitt D w) (Ambient D w)).comp (wittInclusion D w)

theorem ambientInclusion_injective : Function.Injective (ambientInclusion D w) :=
  (IsFractionRing.injective (FieldWitt D w) (Ambient D w)).comp (wittInclusion_injective D w)

def toAmbient : InitialThetaBoundedWittLocalization.Ring D w →+* Ambient D w :=
  IsLocalization.Away.lift (denominator D w) (g := ambientInclusion D w)
    (isUnit_iff_ne_zero.mpr (fun h => denominator_ne_zero D w
      (ambientInclusion_injective D w (h.trans (map_zero _).symm))))

theorem toAmbient_inclusion (a : Ainf D w) :
    toAmbient D w (inclusion D w a) = ambientInclusion D w a :=
  IsLocalization.Away.lift_eq _ _ a

theorem toAmbient_injective : Function.Injective (toAmbient D w) := by
  apply (injective_iff_map_eq_zero (toAmbient D w)).mpr
  intro x hx
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (denominator D w) x
  have ha0 : a = 0 := by
    apply ambientInclusion_injective D w
    rw [map_zero, ← toAmbient_inclusion]
    change toAmbient D w (algebraMap (Ainf D w) (InitialThetaBoundedWittLocalization.Ring D w) a) = 0
    rw [← ha, map_mul, hx, zero_mul]
  rw [ha0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (denominator D w)
    (S := InitialThetaBoundedWittLocalization.Ring D w)).pow n).mul_left_eq_zero.mp ha

/-- A p-power denominator and uniformly bounded, genuine Teichmuller expansion. -/
def HasBoundedExpansion (z : Ambient D w) : Prop :=
  ∃ m : ℕ, ∃ y : FieldWitt D w, ∃ c : ℕ → InitialThetaTiltField.Carrier D w,
    ∃ C : ℝ, 0 < C ∧ (∀ n : ℕ, ‖c n‖ ≤ C) ∧
      Expands (Arithmetic.residueChar w.1) y c ∧
      z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m = algebraMap (FieldWitt D w) (Ambient D w) y

theorem hasBoundedExpansion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    HasBoundedExpansion D w (toAmbient D w x) := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (denominator D w) x
  let v : InitialThetaTiltField.Carrier D w := varpi D w
  have hv : v ≠ 0 := Subtype.coe_ne_coe.mpr (norm_pos_iff.mp (varpi_norm_pos_lt_one D w).1)
  let r := (v ^ m)⁻¹
  let d : ℕ → InitialThetaTiltIntegers.Integers D w := digits (Arithmetic.residueChar w.1) a
  let c : ℕ → InitialThetaTiltField.Carrier D w := fun n =>
    r * (d n : InitialThetaTiltField.Carrier D w)
  let y : FieldWitt D w := WittVector.teichmuller (Arithmetic.residueChar w.1) r * wittInclusion D w a
  refine ⟨m, y, c, ‖r‖, norm_pos_iff.mpr (inv_ne_zero (pow_ne_zero m hv)), ?_, ?_, ?_⟩
  · intro n
    change ‖r * (d n : InitialThetaTiltField.Carrier D w)‖ ≤ ‖r‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      ((LocalGeometricFontaine.mem_integerRing _ _).mp
        (d n).property)
  · exact expands_teichmuller_mul (Arithmetic.residueChar w.1) r _ _
      (expands_map (Arithmetic.residueChar w.1)
        (coefficientInclusion D w)
        a d (expands_digits _ a))
  · have he := congrArg (toAmbient D w) ha
    have hden : ambientInclusion D w (denominator D w) =
        (Arithmetic.residueChar w.1 : Ambient D w) *
          algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller (Arithmetic.residueChar w.1) v) := by
      simp only [denominator, map_mul, map_natCast, ambientInclusion, RingHom.comp_apply,
        wittInclusion, teichVarpi, WittVector.map_teichmuller]
      rfl
    have hrel : toAmbient D w x * ((Arithmetic.residueChar w.1 : Ambient D w) *
        algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller (Arithmetic.residueChar w.1) v)) ^ m =
        ambientInclusion D w a := by
      simp only [map_mul, map_pow] at he
      change toAmbient D w x * toAmbient D w (inclusion D w (denominator D w)) ^ m =
        toAmbient D w (inclusion D w a) at he
      rwa [toAmbient_inclusion, toAmbient_inclusion, hden] at he
    have ht : WittVector.teichmuller (Arithmetic.residueChar w.1) v ≠ 0 := by
      intro h
      have hc := congrArg (fun b : FieldWitt D w => b.coeff 0) h
      exact hv (by simpa only [WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] using hc)
    have htImage : algebraMap (FieldWitt D w) (Ambient D w)
        (WittVector.teichmuller (Arithmetic.residueChar w.1) v) ≠ 0 := by
      intro h
      exact ht (IsFractionRing.injective (FieldWitt D w) (Ambient D w)
        (h.trans (map_zero _).symm))
    apply mul_right_cancel₀ (pow_ne_zero m htImage)
    calc
      (toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m) *
          algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller (Arithmetic.residueChar w.1) v) ^ m =
          ambientInclusion D w a := by rw [mul_assoc, ← mul_pow]; exact hrel
      _ = algebraMap (FieldWitt D w) (Ambient D w) y *
          algebraMap (FieldWitt D w) (Ambient D w) (WittVector.teichmuller (Arithmetic.residueChar w.1) v) ^ m := by
        change algebraMap (FieldWitt D w) (Ambient D w) (wittInclusion D w a) = _
        rw [← map_pow, ← map_mul]
        congr 1
        change wittInclusion D w a =
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r * wittInclusion D w a) *
            WittVector.teichmuller (Arithmetic.residueChar w.1) v ^ m
        rw [mul_right_comm, ← map_pow, ← map_mul]
        simp only [r, inv_mul_cancel₀ (pow_ne_zero m hv), map_one, one_mul]

/-- A bounded expansion can be scaled into the original valuation integers coefficient by coefficient. -/
theorem integral_scaled_expansion (y : FieldWitt D w) (c : ℕ → InitialThetaTiltField.Carrier D w)
    (hc : Expands (Arithmetic.residueChar w.1) y c) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ n : ℕ, ‖c n‖ ≤ C) :
    ∃ k : ℕ, ∃ a : Ainf D w,
      WittVector.teichmuller (Arithmetic.residueChar w.1)
        (varpi D w : InitialThetaTiltField.Carrier D w) ^ k * y = wittInclusion D w a := by
  let v : InitialThetaTiltField.Carrier D w := varpi D w
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hC) (varpi_norm_pos_lt_one D w).2
  have hnorm (n : ℕ) : ‖v ^ k * c n‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg (norm_nonneg v) k)).trans
      ((lt_div_iff₀ hC).mp hk).le
  let d : ℕ → InitialThetaTiltIntegers.Integers D w := fun n =>
    ⟨v ^ k * c n, (LocalGeometricFontaine.mem_integerRing _ _).mpr (hnorm n)⟩
  let a : Ainf D w := WittVector.mk (Arithmetic.residueChar w.1) (fun n => d n ^ (Arithmetic.residueChar w.1 ^ n))
  refine ⟨k, a, ?_⟩
  have he := expands_teichmuller_mul (Arithmetic.residueChar w.1) (v ^ k) y c hc
  rw [map_pow] at he
  apply WittVector.ext
  intro n
  exact ((expands_iff_coeff _ _ _).mp he n)

theorem mem_range_of_hasBoundedExpansion (z : Ambient D w) (hz : HasBoundedExpansion D w z) :
    z ∈ Set.range (toAmbient D w) := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz⟩ := hz
  obtain ⟨k, a, ha⟩ := integral_scaled_expansion D w y c hc C hC hbound
  let b : InitialThetaBoundedWittLocalization.Ring D w :=
    inclusion D w (Arithmetic.residueChar w.1) ^ m * inclusion D w (teichVarpi D w) ^ k
  have hb : IsUnit b := (prime_isUnit D w).pow m |>.mul ((teichVarpi_isUnit D w).pow k)
  obtain ⟨u, hu⟩ := hb
  have he : z * toAmbient D w b = toAmbient D w (inclusion D w a) := by
    change z * toAmbient D w (inclusion D w (Arithmetic.residueChar w.1) ^ m *
      inclusion D w (teichVarpi D w) ^ k) = _
    rw [map_mul, map_pow, map_pow, toAmbient_inclusion, toAmbient_inclusion, toAmbient_inclusion]
    have hp : ambientInclusion D w (Arithmetic.residueChar w.1) =
        (Arithmetic.residueChar w.1 : Ambient D w) := map_natCast _ _
    have ht : ambientInclusion D w (teichVarpi D w) =
        algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1)
            (varpi D w : InitialThetaTiltField.Carrier D w)) := by
      rw [ambientInclusion, RingHom.comp_apply, teichVarpi, wittInclusion, WittVector.map_teichmuller]
      rfl
    rw [hp, ← mul_assoc, hz, ht, ← map_pow, ← map_mul]
    change algebraMap (FieldWitt D w) (Ambient D w) (y * _) =
      algebraMap (FieldWitt D w) (Ambient D w) (wittInclusion D w a)
    rw [mul_comm, ha]
  refine ⟨inclusion D w a * (u⁻¹ : _), ?_⟩
  rw [map_mul, ← he, ← hu, mul_assoc, ← map_mul]
  simp only [Units.mul_inv, map_one, mul_one]

theorem range_eq_boundedExpansions : Set.range (toAmbient D w) = {z | HasBoundedExpansion D w z} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact hasBoundedExpansion D w x
  · exact mem_range_of_hasBoundedExpansion D w z

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittExpansion
