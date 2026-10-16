import ArithmeticTeichmullerSpaces.Act1Scene1.LocalUnitPrincipalPower
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogShellNormalization

/-!
source-id: JT-SCENE1-INTEGER-UNIT-LOGARITHM
source: finite residue-field exponent, actual principal-unit Z_p powers,
standard rational Kummer classes and Joshi III 2843--2853.
fidelity: all integer-ring units have the same rational Kummer image as
principal units. Their logarithm is an additive extension of the existing
principal logarithm, with the usual prime-to-p power formula. Its p*-scaled
image is the old ordinary log-shell. No integral-H1/BK comparison is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
local notation "O" => unitIntegerRing k
local notation "F" => unitResidueField k
variable [hF : Finite (unitResidueField k)] (p : ℕ) [Fact p.Prime]
  [hFp : CharP (unitResidueField k) p]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (hpk : ‖(p : k)‖ < 1)
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)

include hpk hF hFp in
theorem integerUnit_kummer_mem_principalImage (a : Oˣ) :
    (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p (Units.map (unitIntegerRing k).subtype.toMonoidHom a)).toAdd ∈
      principalKummerImage p := by
  let n := unitResidueExponent (k := k)
  have hn : n ≠ 0 := (unitResidueExponent_pos (k := k)).ne'
  have hnorm : ‖(n : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (unitResidueExponent_coprime (k := k) p)
  let r : ℤ_[p] := ⟨(n : ℚ_[p])⁻¹, by
    change ‖(n : ℚ_[p])⁻¹‖ ≤ 1
    simpa only [norm_inv, hnorm, inv_one] using (le_refl (1 : ℝ))⟩
  let b : principalUnits (k := k) :=
    ⟨Units.map (unitIntegerRing k).subtype.toMonoidHom a ^ n, integerUnit_pow_principal (k := k) a⟩
  have hK : principalKummerHom (Ω := Ω) p (Additive.ofMul b) =
      n • (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p (Units.map (unitIntegerRing k).subtype.toMonoidHom a)).toAdd := by
    exact congrArg (fun z : Multiplicative H => z.toAdd)
      (map_pow (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p)
        (Units.map (unitIntegerRing k).subtype.toMonoidHom a) n)
  have hx : n • (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p (Units.map (unitIntegerRing k).subtype.toMonoidHom a)).toAdd ∈
      principalKummerImage p := by
    rw [← hK]
    exact ⟨Additive.ofMul b, rfl⟩
  have h := padicInt_smul_mem_principalKummerImage p hpk r hx
  have hr : (r : ℚ_[p]) = (n : ℚ_[p])⁻¹ := rfl
  simpa only [hr, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn : (n : ℚ_[p]) ≠ 0), one_smul] using h

def integerUnitKummerHom : Additive Oˣ →+ principalKummerImage (k := k) (Ω := Ω) p where
  toFun a := ⟨(LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p (Units.map (unitIntegerRing k).subtype.toMonoidHom a.toMul)).toAdd,
    integerUnit_kummer_mem_principalImage p hpk a.toMul⟩
  map_zero' := Subtype.ext (congrArg (fun z : Multiplicative H => z.toAdd)
    (map_one ((LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p).comp
      (Units.map (unitIntegerRing k).subtype.toMonoidHom))))
  map_add' a b := Subtype.ext (congrArg (fun z : Multiplicative H => z.toAdd)
    (map_mul ((LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p).comp
      (Units.map (unitIntegerRing k).subtype.toMonoidHom)) a.toMul b.toMul))

def integerUnitLog : Additive Oˣ →+ k :=
  (principalImageLog (Ω := Ω) p hpk).comp (integerUnitKummerHom p hpk)

theorem integerUnitLog_of_principal (a : Oˣ) (ha : ‖((a : O) : k) - 1‖ < 1) :
    integerUnitLog (Ω := Ω) p hpk (Additive.ofMul a) = padicLog ((a : O) : k) := by
  let b : Additive (principalUnits (k := k)) := Additive.ofMul ⟨Units.map (unitIntegerRing k).subtype.toMonoidHom a, ha⟩
  exact principalImageLog_class (Ω := Ω) p hpk b

theorem integerUnitLog_power_formula (a : Oˣ) :
    integerUnitLog (Ω := Ω) p hpk (Additive.ofMul a) =
      (unitResidueExponent (k := k) : k)⁻¹ *
        padicLog (((a : O) : k) ^ unitResidueExponent (k := k)) := by
  let n := unitResidueExponent (k := k)
  have hn : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (unitResidueExponent_pos (k := k)).ne'
  have he : (n : k) * integerUnitLog (Ω := Ω) p hpk (Additive.ofMul a) =
      padicLog (((a : O) : k) ^ n) := by
    calc
      _ = integerUnitLog (Ω := Ω) p hpk (n • Additive.ofMul a) := by
        rw [map_nsmul, nsmul_eq_mul]
      _ = _ := integerUnitLog_of_principal p hpk (a ^ n) (integerUnit_pow_principal a)
  rw [← he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- A principal unit is an actual unit of the same valuation integer ring. -/
def principalToIntegerUnit (a : principalUnits (k := k)) : Oˣ where
  val := ⟨(a.1 : k), Valued.toNormedField.norm_le_one_iff.mp
    (norm_eq_one_of_norm_sub_one_lt a.2).le⟩
  inv := ⟨(a.1 : k)⁻¹, Valued.toNormedField.norm_le_one_iff.mp (by
    change ‖(a.1 : k)⁻¹‖ ≤ 1
    rw [norm_inv, norm_eq_one_of_norm_sub_one_lt a.2, inv_one])⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ a.1.ne_zero)
  inv_val := Subtype.ext (inv_mul_cancel₀ a.1.ne_zero)

theorem integerUnitKummerHom_principalToIntegerUnit (a : principalUnits (k := k)) :
    integerUnitKummerHom (Ω := Ω) p hpk (Additive.ofMul (principalToIntegerUnit a)) =
      (principalKummerHom p).rangeRestrict (Additive.ofMul a) := by
  apply Subtype.ext
  rfl

theorem integerUnitKummerHom_surjective :
    Function.Surjective (integerUnitKummerHom (k := k) (Ω := Ω) p hpk) := by
  intro x
  obtain ⟨a, ha⟩ := (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict_surjective x
  exact ⟨Additive.ofMul (principalToIntegerUnit a.toMul),
    (integerUnitKummerHom_principalToIntegerUnit p hpk a.toMul).trans ha⟩

theorem integerUnitLog_principalToIntegerUnit (a : principalUnits (k := k)) :
    integerUnitLog (Ω := Ω) p hpk (Additive.ofMul (principalToIntegerUnit a)) =
      padicLog (a.1 : k) :=
  integerUnitLog_of_principal p hpk _ a.2

theorem integerUnitLog_has_principalRepresentative (a : Oˣ) :
    ∃ b : principalUnits (k := k), integerUnitLog (Ω := Ω) p hpk (Additive.ofMul a) =
      padicLog (b.1 : k) := by
  obtain ⟨b, hb⟩ := (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict_surjective
    (integerUnitKummerHom (Ω := Ω) p hpk (Additive.ofMul a))
  exact ⟨b.toMul, (congrArg (principalImageLog p hpk) hb).symm.trans
    (principalImageLog_class p hpk b)⟩

theorem integerUnitLog_continuous :
    Continuous (fun a : Oˣ => integerUnitLog (Ω := Ω) p hpk (Additive.ofMul a)) := by
  have hv : Continuous (fun a : Oˣ => ((a : O) : k)) :=
    continuous_subtype_val.comp Units.continuous_val
  have he : (fun a : Oˣ => integerUnitLog (Ω := Ω) p hpk (Additive.ofMul a)) =
      fun a : Oˣ => (unitResidueExponent (k := k) : k)⁻¹ *
        padicLog (((a : O) : k) ^ unitResidueExponent (k := k)) :=
    funext (integerUnitLog_power_formula p hpk)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro a
  have hp : ContinuousAt
      (fun b : Oˣ => ((b : O) : k) ^ unitResidueExponent (k := k)) a :=
    (hv.pow (unitResidueExponent (k := k))).continuousAt
  have hl : ContinuousAt (padicLog : k → k)
      (((a : O) : k) ^ unitResidueExponent (k := k)) :=
    continuousAt_padicLog_principal hpk (integerUnit_pow_principal a)
  exact continuousAt_const.mul
    (hl.comp (f := fun b : Oˣ => ((b : O) : k) ^ unitResidueExponent (k := k)) hp)

def paperIntegerUnitLogShell : Set k :=
  {y | ∃ a : Oˣ, y = (paperScale p : k)⁻¹ * integerUnitLog (Ω := Ω) p hpk (Additive.ofMul a)}

variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]

theorem logShell_eq_paperIntegerUnitLogShell :
    logShell (k := k) p = paperIntegerUnitLogShell (Ω := Ω) p hpk := by
  rw [logShell_eq_paperPrincipalLogShell p hpk]
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    let b : principalUnits (k := k) := ⟨Units.mk0 a (ne_zero_of_norm_sub_one_lt ha), ha⟩
    exact ⟨principalToIntegerUnit b, by rw [integerUnitLog_principalToIntegerUnit]; rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := integerUnitLog_has_principalRepresentative (Ω := Ω) p hpk a
    exact ⟨b.1, b.2, by rw [hb]⟩

end
end JoshiTeich.Act1Scene1.LocalPadicLog
