import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogShell
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicPaperLog

/-!
source-id: JT-SCENE1-KUMMER-LOG-SHELL-NORMALIZATION
source: Joshi III 2843--2853, 3160--3175 and 3226; the existing
ordinary 2p-normalized shell and actual principal-unit p-adic powers.
fidelity: p*-normalized principal logarithms have exactly the same carrier
as the old 2p-normalized shell. The corresponding original H1 shell has
actual p*-divided principal Kummer representatives. No BK identity is used.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)
variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]

/-- This definition concerns principal units; no decomposition of all units is assumed. -/
def paperPrincipalLogShell : Set k :=
  {y | ∃ a : k, ‖a - 1‖ < 1 ∧ y = (paperScale p : k)⁻¹ * padicLog a}

include hpk in
theorem logShell_eq_paperPrincipalLogShell : logShell (k := k) p = paperPrincipalLogShell p := by
  by_cases hp2 : p = 2
  · subst p
    norm_num [logShell, paperPrincipalLogShell, paperScale]
  have hn : ‖(2 : ℚ_[p])‖ = 1 := by
    exact Padic.norm_natCast_eq_one_iff.mpr
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)))
  let r : ℤ_[p] := ⟨(2 : ℚ_[p])⁻¹, by
    change ‖(2 : ℚ_[p])⁻¹‖ ≤ 1
    simpa only [norm_inv, hn, inv_one] using (le_refl (1 : ℝ))⟩
  have hr : (r : ℚ_[p]) = (2 : ℚ_[p])⁻¹ := rfl
  have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    let u : principalUnits (k := k) :=
      ⟨Units.mk0 a (ne_zero_of_norm_sub_one_lt ha), ha⟩
    refine ⟨(principalPadicPower hpk u r : kˣ), (principalPadicPower hpk u r).2, ?_⟩
    rw [padicLog_principalPadicPower hpk u r, hr]
    simp only [paperScale, if_neg hp2, Algebra.smul_def, map_inv₀, map_ofNat]
    change (2 * (p : k))⁻¹ * padicLog a = (p : k)⁻¹ * (2⁻¹ * padicLog a)
    field_simp [hp0] <;> ring
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a ^ 2, norm_pow_sub_one_lt ha 2, ?_⟩
    rw [padicLog_pow (Fact.out : p.Prime) hpk ha 2]
    simp only [paperScale, if_neg hp2, Nat.cast_ofNat]
    field_simp [hp0] <;> ring

variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω]

def paperPrincipalSaturatedClass (a : Additive (principalUnits (k := k))) :
    saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk :=
  (paperScale p : ℚ_[p])⁻¹ • principalSaturatedClass p hpk a

theorem saturatedPadicLog_paperPrincipalClass (a : Additive (principalUnits (k := k))) :
    saturatedPadicLog p hpk (paperPrincipalSaturatedClass (Ω := Ω) p hpk a) =
      (paperScale p : k)⁻¹ * padicLog (a.toMul.1 : k) := by
  change saturatedPadicLog p hpk ((paperScale p : ℚ_[p])⁻¹ • _) = _
  rw [map_smul, saturatedPadicLog_principalSaturatedClass]
  simp only [Algebra.smul_def, map_inv₀, map_natCast]

theorem mem_normalizedKummerShell_iff_paperScale
    (x : saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk) :
    x ∈ normalizedKummerShell p hpk ↔
      ∃ a : Additive (principalUnits (k := k)), paperPrincipalSaturatedClass p hpk a = x := by
  change saturatedPadicLog p hpk x ∈ logShell p ↔ _
  rw [logShell_eq_paperPrincipalLogShell p hpk]
  constructor
  · rintro ⟨a, ha, hlog⟩
    let u : principalUnits (k := k) :=
      ⟨Units.mk0 a (ne_zero_of_norm_sub_one_lt ha), ha⟩
    refine ⟨Additive.ofMul u, (saturatedPadicLogEquiv p hpk).injective ?_⟩
    exact (saturatedPadicLog_paperPrincipalClass (Ω := Ω) p hpk _).trans hlog.symm
  · rintro ⟨a, rfl⟩
    rw [saturatedPadicLog_paperPrincipalClass]
    exact ⟨a.toMul.1, a.toMul.2, rfl⟩

end
end JoshiTeich.Act1Scene1.LocalPadicLog
