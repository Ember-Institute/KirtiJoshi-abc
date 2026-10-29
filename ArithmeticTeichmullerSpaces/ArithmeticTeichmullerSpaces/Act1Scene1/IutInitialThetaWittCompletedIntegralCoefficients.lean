import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNonnegativeCoefficientCauchy
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittInverseRadiusOrbit

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-COMPLETED-INTEGRAL-COEFFICIENTS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, integral
coefficients of bounded elements in the original common completion.
fidelity: nonnegative original Witt source norms are monotone in radius.
The constructed approximants along inverse Frobenius radii therefore
have unit bounds at the base radius. Their coefficients are Cauchy in
the original complete tilt field. Unit bounds at radii tending to one
force the coefficient limits into its original valuation integers,
constructing one actual Ainf vector. No integral input approximants or
coefficient limit law is assumed. Original proofs; no code copied.
boundary: Scene1/Derived; equality of the resulting Ainf image with
the completed element is a separate convergence step. R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittCompletedIntegralCoefficients

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion WittTeichmullerExpansion
open InitialThetaWittAllRadiusCompletion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem realValue_mono_of_nonnegative (s t : Radius) (hst : s.val ≤ t.val)
    (a : InitialThetaBoundedWittLocalization.Ring D w) (b : FieldWitt D w)
    (hab : toAmbient D w a = algebraMap (FieldWitt D w) (Ambient D w) b) :
    InitialThetaWittRhoNorm.realValue D w s.val a ≤
      InitialThetaWittRhoNorm.realValue D w t.val a := by
  have he (r : Radius) : InitialThetaWittRhoValue.value D w r.val a =
      WittWeightedDigits.value (Arithmetic.residueChar w.1) r.val b := by
    have hpres : toAmbient D w a * (Arithmetic.residueChar w.1 : Ambient D w) ^ 0 =
        algebraMap (FieldWitt D w) (Ambient D w) b := by simpa only [pow_zero, mul_one] using hab
    simpa only [pow_zero, div_one] using InitialThetaWittRhoValue.value_eq_of_presentation
      D w r.val r.property.1.ne' (r.property.2.trans ENNReal.one_lt_top).ne a 0 b hpres
  have hval : InitialThetaWittRhoValue.value D w s.val a ≤
      InitialThetaWittRhoValue.value D w t.val a := by
    rw [he s, he t]
    apply iSup_le
    intro i
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ bot_le hst i) bot_le).trans
      (WittWeightedDigits.term_le_value (Arithmetic.residueChar w.1) t.val b i)
  exact ENNReal.toReal_mono
    (InitialThetaWittRhoValue.value_lt_top D w t.val t.property.1.ne' t.property.2.le a).ne hval

theorem base_le_inverse_orbit (ρ : Radius) (n : ℕ) :
    ρ.val ≤ (InitialThetaWittInverseRadiusOrbit.orbit D w ρ n).val := by
  induction n with
  | zero => rw [InitialThetaWittInverseRadiusOrbit.orbit_zero]
  | succ n ih =>
    apply ih.trans
    have h := InitialThetaWittInverseRadiusOrbit.powered_orbit_succ D w ρ n
    have hp : (InitialThetaWittInverseRadiusOrbit.orbit D w ρ (n + 1)).val ^
        Arithmetic.residueChar w.1 ≤ (InitialThetaWittInverseRadiusOrbit.orbit D w ρ (n + 1)).val := by
      simpa only [pow_one] using pow_le_pow_of_le_one
        (InitialThetaWittInverseRadiusOrbit.orbit D w ρ (n + 1)).property.1.le
        (InitialThetaWittInverseRadiusOrbit.orbit D w ρ (n + 1)).property.2.le
        (Arithmetic.residueChar_prime w.1).one_lt.le
    change (InitialThetaWittRhoFrobeniusCompletion.poweredRadius D w
      (InitialThetaWittInverseRadiusOrbit.orbit D w ρ (n + 1))).val ≤ _ at hp
    rwa [h] at hp

theorem exists_integral_coefficient_limit (ρ : Radius)
    (t : ℕ → Radius) (ht : Filter.Tendsto (fun k => (t k).val.toReal) Filter.atTop (𝓝 1))
    (a : ℕ → InitialThetaBoundedWittLocalization.Ring D w) (b : ℕ → FieldWitt D w)
    (hab : ∀ k, toAmbient D w (a k) = algebraMap (FieldWitt D w) (Ambient D w) (b k))
    (hb : ∀ k, InitialThetaWittRhoNorm.realValue D w ρ.val (a k) ≤ 1)
    (htb : ∀ k, InitialThetaWittRhoNorm.realValue D w (t k).val (a k) ≤ 1)
    (ha : CauchySeq (fun k => InitialThetaWittRhoCompletion.inclusion D w ρ (a k))) :
    ∃ c : InitialThetaTiltFontaine.Ainf D w, ∀ i : ℕ,
      Filter.Tendsto (fun k => (b k).coeff i) Filter.atTop
        (𝓝 (c.coeff i : InitialThetaTiltField.Carrier D w)) := by
  have hlim : ∀ i : ℕ, ∃ c : InitialThetaTiltField.Carrier D w,
      Filter.Tendsto (fun k => (b k).coeff i) Filter.atTop (𝓝 c) := fun i =>
    cauchySeq_tendsto_of_complete
      (InitialThetaWittNonnegativeCoefficientCauchy.cauchySeq_coeff D w ρ a b hab hb ha i)
  choose c hc using hlim
  have hi (i : ℕ) : c i ∈ InitialThetaTiltIntegers.Integers D w := by
    apply (LocalGeometricFontaine.mem_integerRing _ _).mpr
    have hnorm (k : ℕ) : ‖(b k).coeff i‖ * ((t k).val.toReal ^ i) ^
        (Arithmetic.residueChar w.1 ^ i) ≤ 1 := by
      have h := InitialThetaWittNonnegativeCoefficientCauchy.digit_norm_le_div
        D w (t k) (a k) (b k) (hab k) i i le_rfl
      have hp : 0 < (t k).val.toReal ^ i := pow_pos
        (ENNReal.toReal_pos (t k).property.1.ne' ((t k).property.2.trans ENNReal.one_lt_top).ne) i
      have hmul : ‖digits (Arithmetic.residueChar w.1) (b k) i‖ * (t k).val.toReal ^ i ≤ 1 :=
        ((le_div_iff₀ hp).mp h).trans (htb k)
      rw [(expands_iff_coeff _ _ _).mp (expands_digits _ (b k)) i, norm_pow, ← mul_pow]
      exact pow_le_one₀ (mul_nonneg (norm_nonneg _) hp.le) hmul
    have hl := (hc i).norm.mul ((ht.pow i).pow (Arithmetic.residueChar w.1 ^ i))
    have hbound := le_of_tendsto hl (Filter.Eventually.of_forall hnorm)
    simpa only [one_pow, mul_one] using hbound
  exact ⟨WittVector.mk (Arithmetic.residueChar w.1) (fun i => ⟨c i, hi i⟩), hc⟩

theorem exists_completed_integral_coefficients (ρ : Radius) (x : Carrier D w)
    (hx : ∀ r : Radius, ‖evaluate D w r x‖ ≤ 1) :
    ∃ a : ℕ → InitialThetaBoundedWittLocalization.Ring D w, ∃ b : ℕ → FieldWitt D w,
      ∃ c : InitialThetaTiltFontaine.Ainf D w,
      (∀ k, toAmbient D w (a k) = algebraMap (FieldWitt D w) (Ambient D w) (b k)) ∧
      (∀ k, InitialThetaWittRhoNorm.realValue D w
        (InitialThetaWittInverseRadiusOrbit.orbit D w ρ k).val (a k) ≤ 1) ∧
      Filter.Tendsto (fun k => InitialThetaWittRhoCompletion.inclusion D w ρ (a k))
        Filter.atTop (𝓝 (evaluate D w ρ x)) ∧
      (∀ i : ℕ, Filter.Tendsto (fun k => (b k).coeff i) Filter.atTop
        (𝓝 (c.coeff i : InitialThetaTiltField.Carrier D w))) := by
  obtain ⟨a, b, hab, hunit, ha⟩ :=
    InitialThetaWittCompletedNonnegativeApproximation.exists_nonnegative_approximating_sequence
      D w ρ (InitialThetaWittInverseRadiusOrbit.orbit D w ρ) x hx
  have hb (k : ℕ) : InitialThetaWittRhoNorm.realValue D w ρ.val (a k) ≤ 1 :=
    (realValue_mono_of_nonnegative D w ρ _ (base_le_inverse_orbit D w ρ k)
      (a k) (b k) (hab k)).trans (hunit k)
  obtain ⟨c, hc⟩ := exists_integral_coefficient_limit D w ρ _
    (InitialThetaWittInverseRadiusOrbit.orbit_toReal_tendsto_one D w ρ) a b hab hb hunit ha.cauchySeq
  exact ⟨a, b, c, hab, hunit, ha, hc⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittCompletedIntegralCoefficients
