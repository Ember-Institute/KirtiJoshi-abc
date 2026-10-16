import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicPowerClass
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedLogEquivalence

/-!
source-id: JT-SCENE1-SATURATED-KUMMER-PADIC-MODULE
source: actual principal-unit Kummer Z_p scalar comparison and p-power
denominator clearing in Q_p; Joshi III 3212--3226.
fidelity: the existing saturated subgroup is closed under the original Q_p
action on standard H1. Its ordinary logarithm is Q_p linear for the existing
continuous local-field action and gives a linear equivalence. H1e/BK and
topological identification are not inferred from this linear equivalence.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)
local notation "I" => principalKummerImage (k := k) (Ω := Ω) p

def principalImagePadicSmul (r : ℤ_[p]) (a : I) : I :=
  ⟨(r : ℚ_[p]) • (a : H), padicInt_smul_mem_principalKummerImage p hpk r a.2⟩

include hpk in
theorem padic_smul_mem_saturatedKummerImage (r : ℚ_[p]) {x : H}
    (hx : x ∈ saturatedKummerImage p) : r • x ∈ saturatedKummerImage p := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, z, hz⟩ := LocalKummer.Rational.exists_integral_p_power_mul p r
  refine ⟨n + m, ?_⟩
  have he : (p ^ (n + m)) • (r • x) = (z : ℚ_[p]) • ((p ^ n) • x) := by
    simp only [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow, smul_smul]
    rw [hz, pow_add]
    congr 1
    ring
  rw [he]
  exact padicInt_smul_mem_principalKummerImage p hpk z hn

/-- This submodule uses the original scalar action on standard H1. -/
def saturatedKummerPadicSubmodule : Submodule ℚ_[p] H where
  toAddSubmonoid := (saturatedKummerImage p).toAddSubmonoid
  smul_mem' r x hx := padic_smul_mem_saturatedKummerImage p hpk r hx

theorem saturated_as_divided_image (x : saturatedKummerImage (k := k) (Ω := Ω) p)
    (n : ℕ) (hn : (p ^ n) • (x : H) ∈ I) :
    x = saturatedClassOfImage p ⟨(p ^ n) • (x : H), hn⟩ n := by
  apply Subtype.ext
  change (x : H) = ((p : ℚ_[p]) ^ n)⁻¹ • ((p ^ n) • (x : H))
  rw [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)), one_smul]

variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]

theorem principalImageLog_padicSmul (r : ℤ_[p]) (a : I) :
    principalImageLog p hpk (principalImagePadicSmul p hpk r a) =
      (r : ℚ_[p]) • principalImageLog p hpk a := by
  obtain ⟨b, hb⟩ := (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict_surjective a
  subst a
  have he : principalImagePadicSmul p hpk r
      ((principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict b) =
      (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict
        (Additive.ofMul (principalPadicPower hpk b.toMul r)) := by
    apply Subtype.ext
    exact (principalKummerHom_principalPadicPower p hpk b.toMul r).symm
  rw [he, principalImageLog_class, principalImageLog_class]
  exact padicLog_principalPadicPower hpk b.toMul r

theorem saturatedImageLog_padic_smul (r : ℚ_[p])
    (x : saturatedKummerImage (k := k) (Ω := Ω) p) :
    saturatedImageLog p hpk
        ⟨r • (x : H), padic_smul_mem_saturatedKummerImage p hpk r x.2⟩ =
      r • saturatedImageLog p hpk x := by
  obtain ⟨n, hn⟩ := x.2
  let a : I := ⟨(p ^ n) • (x : H), hn⟩
  obtain ⟨m, z, hz⟩ := LocalKummer.Rational.exists_integral_p_power_mul p r
  have he : (⟨r • (x : H), padic_smul_mem_saturatedKummerImage p hpk r x.2⟩ :
      saturatedKummerImage p) = saturatedClassOfImage p (principalImagePadicSmul p hpk z a) (n + m) := by
    apply Subtype.ext
    change r • (x : H) = ((p : ℚ_[p]) ^ (n + m))⁻¹ •
      ((z : ℚ_[p]) • ((p ^ n) • (x : H)))
    rw [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow, smul_smul, smul_smul, hz]
    congr 1
    rw [pow_add]
    field_simp [show (p : ℚ_[p]) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero] <;> ring
  have hx : saturatedImageLog p hpk x = ((p : k) ^ n)⁻¹ * principalImageLog p hpk a :=
    (congrArg (saturatedImageLog p hpk) (saturated_as_divided_image p x n hn)).trans
      (saturatedImageLog_classOfImage p hpk a n)
  rw [he, saturatedImageLog_classOfImage, principalImageLog_padicSmul, hx]
  simp only [Algebra.smul_def]
  rw [hz, map_mul, map_pow, map_natCast]
  rw [pow_add]
  field_simp [show (p : k) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero] <;> ring

def saturatedPadicLog : saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk →ₗ[ℚ_[p]] k where
  toFun x := saturatedImageLog p hpk ⟨x.1, x.2⟩
  map_add' x y := map_add (saturatedImageLog p hpk) ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
  map_smul' r x := saturatedImageLog_padic_smul p hpk r ⟨x.1, x.2⟩

/-- The linear comparison retains the original H1 classes and both scalar actions. -/
def saturatedPadicLogEquiv :
    saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk ≃ₗ[ℚ_[p]] k :=
  LinearEquiv.ofBijective (saturatedPadicLog p hpk) ⟨by
    intro x y h
    exact Subtype.ext (congrArg Subtype.val (saturatedImageLog_injective p hpk h)), by
    intro y
    obtain ⟨x, hx⟩ := saturatedImageLog_surjective (Ω := Ω) p hpk y
    exact ⟨⟨x.1, x.2⟩, hx⟩⟩

end
end JoshiTeich.Act1Scene1.LocalPadicLog
