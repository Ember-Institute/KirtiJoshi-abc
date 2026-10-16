import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionUnitLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionQOrderPower
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerDividedIntegralLift

/-!
source-id: JT-SCENE1-COMPLETION-KUMMER-UNIT-CRITERION
source: actual discrete completion valuation, Kummer root descent and the
finite-residue-field unit image; Joshi III 3190--3236.
fidelity: identifies which multiplicative Kummer classes belong to the
existing saturated principal-unit subspace by the actual norm-one condition.
No surjectivity onto ambient H1 or identification with H1e/BK is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open NumberField JoshiTeich.Prologue
open scoped Valued
universe u v
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
variable (p : ℕ) [Fact p.Prime]

theorem no_baseRootTower_of_contracting (a : completionAt K w)
    (ha : a ≠ 0) (ha1 : ‖a‖ < 1) :
    ¬ Nonempty (LocalKummer.RootTower (K := completionAt K w) (Ω := completionAt K w) p a) := by
  rintro ⟨R⟩
  let q := Arithmetic.completionQOrder w a
  have hq : 0 < q := Arithmetic.completionQOrder_pos w a ha ha1
  have hd : p ^ q ∣ q := qOrder_dvd_of_power_root w a ha ha1 (p ^ q)
    (pow_pos (Fact.out : p.Prime).pos _) (R.root q)
    (by simpa only [Algebra.algebraMap_self_apply] using R.root_pow_eq q)
  exact (Nat.not_le.mpr (Nat.lt_pow_self (Fact.out : p.Prime).one_lt))
    (Nat.le_of_dvd hq hd)

theorem norm_eq_one_of_baseRootTower (a : completionAt K w) (ha : a ≠ 0)
    (R : LocalKummer.RootTower (K := completionAt K w) (Ω := completionAt K w) p a) :
    ‖a‖ = 1 := by
  rcases lt_trichotomy ‖a‖ 1 with h | h | h
  · exact False.elim (no_baseRootTower_of_contracting w p a ha h ⟨R⟩)
  · exact h
  · let S : LocalKummer.RootTower (K := completionAt K w) (Ω := completionAt K w) p a⁻¹ :=
      { root := fun n => (R.root n)⁻¹
        root_zero := by simp only [R.root_zero, Algebra.algebraMap_self_apply]
        root_succ := fun n => by rw [inv_pow, R.root_succ] }
    exact False.elim (no_baseRootTower_of_contracting w p a⁻¹ (inv_ne_zero ha)
      (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h) ⟨S⟩)

variable {Ω : Type v} [Field Ω] [Algebra (completionAt K w) Ω]
variable [Algebra.IsIntegral (completionAt K w) Ω] [IsGalois (completionAt K w) Ω]
variable [CharZero Ω] [IsAlgClosed Ω]

theorem norm_eq_one_of_rationalKummer_eq_zero (a : (completionAt K w)ˣ)
    (ha : (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd = 0) :
    ‖(a : completionAt K w)‖ = 1 := by
  let R := LocalKummer.rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : completionAt K w)
  obtain ⟨n, hn, hz⟩ := LocalKummer.Rational.integral_powClass_eq_zero_of_rational_eq_zero
    p R a.ne_zero ha
  obtain ⟨S⟩ := ((R.pow (p ^ n)).padicClass_eq_zero_iff_baseTower hn).mp hz
  have h := norm_eq_one_of_baseRootTower w p _ hn S
  rw [norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp h

variable (hpw : Arithmetic.residueChar w = p)
local instance unitCriterionCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local instance unitCriterionResidueFinite :
    Finite (LocalPadicLog.unitResidueField (completionAt K w)) := integerResidue_finite w
private theorem norm_prime_lt_one (hpw : Arithmetic.residueChar w = p) :
    ‖(p : completionAt K w)‖ < 1 := by
  have h := norm_natCast_prime_lt_one hpw
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

/-- A norm-one field unit is a unit of the original completion integer ring. -/
def normOneIntegerUnit (a : (completionAt K w)ˣ) (ha : ‖(a : completionAt K w)‖ = 1) :
    (integerRing w)ˣ where
  val := ⟨(a : completionAt K w), Valued.toNormedField.norm_le_one_iff.mp ha.le⟩
  inv := ⟨(a : completionAt K w)⁻¹, Valued.toNormedField.norm_le_one_iff.mp (by
    change ‖(a : completionAt K w)⁻¹‖ ≤ 1
    rw [norm_inv, ha, inv_one])⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ a.ne_zero)
  inv_val := Subtype.ext (inv_mul_cancel₀ a.ne_zero)

theorem rationalKummer_mem_principalImage_of_norm_eq_one
    (hpw : Arithmetic.residueChar w = p) (a : (completionAt K w)ˣ)
    (ha : ‖(a : completionAt K w)‖ = 1) :
    (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd ∈
      LocalPadicLog.principalKummerImage p := by
  letI : CharP (LocalPadicLog.unitResidueField (completionAt K w)) p := by
    rw [← hpw]
    exact integerResidue_charP w
  have h := LocalPadicLog.integerUnit_kummer_mem_principalImage (Ω := Ω) p
    (norm_prime_lt_one w p hpw) (normOneIntegerUnit w a ha)
  convert h using 1
  exact congrArg (fun b => (LocalKummer.Rational.kummerHom (Ω := Ω) p b).toAdd)
    (Units.ext rfl)

theorem rationalKummer_mem_saturated_iff_norm_eq_one
    (hpw : Arithmetic.residueChar w = p) (a : (completionAt K w)ˣ) :
    (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd ∈
      LocalPadicLog.saturatedKummerImage p ↔ ‖(a : completionAt K w)‖ = 1 := by
  constructor
  · rintro ⟨n, b, hb⟩
    let c : (completionAt K w)ˣ := a ^ (p ^ n) / b.toMul.1
    have hc : (LocalKummer.Rational.kummerHom (Ω := Ω) p c).toAdd = 0 := by
      change (LocalKummer.Rational.kummerHom (Ω := Ω) p
        (a ^ (p ^ n) / b.toMul.1)).toAdd = 0
      rw [map_div, toAdd_div, LocalKummer.Rational.kummerHom_pow_nsmul]
      exact sub_eq_zero.mpr hb.symm
    have hn := norm_eq_one_of_rationalKummer_eq_zero w p c hc
    have hb1 : ‖(b.toMul.1 : completionAt K w)‖ = 1 :=
      LocalPadicLog.norm_eq_one_of_norm_sub_one_lt b.toMul.2
    dsimp only [c] at hn
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at hn
    rw [norm_div, norm_pow, hb1, div_one] at hn
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp hn
  · intro ha
    exact ⟨0, by simpa only [pow_zero, one_nsmul] using
      rationalKummer_mem_principalImage_of_norm_eq_one w p hpw a ha⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion
