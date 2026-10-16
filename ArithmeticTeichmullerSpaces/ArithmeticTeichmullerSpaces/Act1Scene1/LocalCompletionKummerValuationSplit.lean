import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerUnitCriterion
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegree

/-!
source-id: JT-SCENE1-COMPLETION-KUMMER-VALUATION-SPLIT
source: actual completion valuation of the residue prime, ordinary
multiplicative Kummer classes and their unit criterion; Joshi III 3190--3236.
fidelity: separates the Q_p span of all multiplicative Kummer classes into
the existing saturated unit subspace and the residue-prime line, with zero
intersection. The valuation correction is constructed in the original field.
This span is not asserted to be all H1, or its unit part H1e/BK.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
open NumberField JoshiTeich.Prologue WithZero
open scoped Valued
universe u v
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
variable (p : ℕ) [Fact p.Prime] (hpw : Arithmetic.residueChar w = p)
variable {Ω : Type v} [Field Ω] [Algebra (completionAt K w) Ω]
variable [Algebra.IsIntegral (completionAt K w) Ω] [IsGalois (completionAt K w) Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
local instance splitCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep
  (K := completionAt K w) (Ω := Ω) p)

def primeUnit : (completionAt K w)ˣ :=
  Units.mk0 p (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

def kummer (a : (completionAt K w)ˣ) : H :=
  (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd

def valuationIndex (a : (completionAt K w)ˣ) : ℤ := log (Valued.v (a : completionAt K w))

theorem primeUnit_valuation (hpw : Arithmetic.residueChar w = p) :
    Valued.v (primeUnit w p : completionAt K w) = exp (-(Arithmetic.ramIdx w : ℤ)) := by
  have h := valued_residueChar w
  rw [map_natCast, hpw] at h
  exact h

theorem prime_norm_lt_one (hpw : Arithmetic.residueChar w = p) :
    ‖(primeUnit w p : completionAt K w)‖ < 1 := by
  have h := norm_natCast_prime_lt_one hpw
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

def unitsSubspace : Submodule ℚ_[p] H :=
  LocalPadicLog.saturatedKummerPadicSubmodule p (prime_norm_lt_one w p hpw)

/-- Raising to the absolute ramification index permits an integral correction
using the residue prime, without choosing a uniformizer. -/
def correctedUnit (a : (completionAt K w)ˣ) : (completionAt K w)ˣ :=
  a ^ Arithmetic.ramIdx w * primeUnit w p ^ valuationIndex w a

theorem correctedUnit_norm (hpw : Arithmetic.residueChar w = p) (a : (completionAt K w)ˣ) :
    ‖(correctedUnit w p a : completionAt K w)‖ = 1 := by
  apply Valued.toNormedField.norm_eq_one_iff.mpr
  have ha : Valued.v (a : completionAt K w) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  dsimp only [correctedUnit]
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
  rw [map_mul, map_pow, map_zpow₀, primeUnit_valuation w p hpw,
    ← exp_log ha, ← exp_nsmul, ← exp_zsmul, ← exp_add]
  simp only [nsmul_eq_mul, zsmul_eq_mul]
  change exp ((Arithmetic.ramIdx w : ℤ) * valuationIndex w a +
    valuationIndex w a * -(Arithmetic.ramIdx w : ℤ)) = 1
  rw [show (Arithmetic.ramIdx w : ℤ) * valuationIndex w a +
    valuationIndex w a * -(Arithmetic.ramIdx w : ℤ) = 0 by ring, exp_zero]

theorem correctedUnit_kummer (a : (completionAt K w)ˣ) :
    kummer w p (Ω := Ω) (correctedUnit w p a) =
      (Arithmetic.ramIdx w : ℚ_[p]) • kummer w p a +
        (valuationIndex w a : ℚ_[p]) • kummer w p (primeUnit w p) := by
  unfold kummer correctedUnit
  rw [map_mul, toAdd_mul, map_pow, toAdd_pow, map_zpow, toAdd_zpow]
  simp only [Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]

theorem correctedUnit_kummer_mem (a : (completionAt K w)ˣ) :
    kummer w p (Ω := Ω) (correctedUnit w p a) ∈ unitsSubspace w p hpw :=
  (rationalKummer_mem_saturated_iff_norm_eq_one w p hpw _).mpr
    (correctedUnit_norm w p hpw a)

theorem kummer_decomposition (a : (completionAt K w)ˣ) :
    kummer w p (Ω := Ω) a =
      (Arithmetic.ramIdx w : ℚ_[p])⁻¹ • kummer w p (correctedUnit w p a) -
        ((valuationIndex w a : ℚ_[p]) / Arithmetic.ramIdx w) •
          kummer w p (primeUnit w p) := by
  rw [correctedUnit_kummer w p, smul_add, smul_smul, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast (Arithmetic.ramIdx_pos w).ne'), one_smul]
  rw [div_eq_mul_inv, mul_comm (valuationIndex w a : ℚ_[p])]
  exact (add_sub_cancel_right _ _).symm

def multiplicativeSpan : Submodule ℚ_[p] H :=
  Submodule.span ℚ_[p] (Set.range (kummer w p (Ω := Ω)))

def primeLine : Submodule ℚ_[p] H :=
  Submodule.span ℚ_[p] {kummer w p (Ω := Ω) (primeUnit w p)}

theorem unitsSubspace_le_multiplicativeSpan :
    unitsSubspace w p hpw (Ω := Ω) ≤ multiplicativeSpan w p := by
  intro x hx
  obtain ⟨n, a, ha⟩ := hx
  have ha' : (p ^ n) • x = kummer w p (Ω := Ω) a.toMul.1 := ha.symm
  have hm : (p ^ n) • x ∈ multiplicativeSpan w p (Ω := Ω) := by
    rw [ha']
    exact Submodule.subset_span ⟨a.toMul.1, rfl⟩
  have h := (multiplicativeSpan w p (Ω := Ω)).smul_mem ((p : ℚ_[p]) ^ n)⁻¹ hm
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simpa only [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero n hp0), one_smul] using h

theorem multiplicativeSpan_eq_units_sup_primeLine :
    multiplicativeSpan w p (Ω := Ω) = unitsSubspace w p hpw ⊔ primeLine w p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    rw [kummer_decomposition w p a]
    apply (unitsSubspace w p hpw ⊔ primeLine w p (Ω := Ω)).sub_mem
    · exact Submodule.mem_sup_left ((unitsSubspace w p hpw).smul_mem _
        (correctedUnit_kummer_mem w p hpw a))
    · exact Submodule.mem_sup_right ((primeLine w p).smul_mem _
        (Submodule.subset_span (Set.mem_singleton _)))
  · apply sup_le (unitsSubspace_le_multiplicativeSpan w p hpw)
    apply Submodule.span_le.mpr
    rintro x ⟨rfl⟩
    exact Submodule.subset_span ⟨primeUnit w p, rfl⟩

theorem prime_kummer_not_mem_units :
    kummer w p (Ω := Ω) (primeUnit w p) ∉ unitsSubspace w p hpw := by
  intro h
  have hn := (rationalKummer_mem_saturated_iff_norm_eq_one w p hpw _).mp h
  exact (prime_norm_lt_one w p hpw).ne hn

theorem units_disjoint_primeLine :
    Disjoint (unitsSubspace w p hpw (Ω := Ω)) (primeLine w p) :=
  Submodule.disjoint_span_singleton_of_notMem (prime_kummer_not_mem_units w p hpw)

end
end JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
