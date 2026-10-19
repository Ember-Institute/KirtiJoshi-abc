import ArithmeticTeichmullerSpaces.Act1Scene1.AlgebraicallyClosedFontaine
import Mathlib.RingTheory.Localization.Away.Basic

/-!
source-id: JT-SCENE1-NORMED-INTEGER-LOCALIZATION
source: Joshi II untilt field evaluation after the integral eta_K map;
the valuation integer ring and powers of a contracting nonzero element.
fidelity: proves that the original valued field is the localization of its
actual norm valuation integers at a nonzero contraction. No fraction-field
or localization certificate is input. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.NormedIntegerLocalization

noncomputable section
variable (Ω : Type*) [NormedField Ω] [IsUltrametricDist Ω]

theorem exists_integral_multiple (s : LocalGeometricFontaine.integerRing Ω)
    (hs : ‖(s : Ω)‖ < 1) (x : Ω) :
    ∃ n : ℕ, ∃ a : LocalGeometricFontaine.integerRing Ω, x * (s : Ω) ^ n = (a : Ω) := by
  by_cases hx : x = 0
  · exact ⟨0, 0, by simp [hx]⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hxpos) hs
  have ha : x * (s : Ω) ^ n ∈ LocalGeometricFontaine.integerRing Ω := by
    rw [LocalGeometricFontaine.mem_integerRing, norm_mul, norm_pow]
    simpa only [mul_comm] using ((lt_div_iff₀ hxpos).mp hn).le
  exact ⟨n, ⟨x * (s : Ω) ^ n, ha⟩, rfl⟩

theorem field_isLocalization (s : LocalGeometricFontaine.integerRing Ω)
    (hs0 : s ≠ 0) (hs1 : ‖(s : Ω)‖ < 1) : IsLocalization.Away s Ω := by
  apply IsLocalization.Away.mk s
  · exact isUnit_iff_ne_zero.mpr (Subtype.coe_ne_coe.mpr hs0)
  · intro x
    exact exists_integral_multiple Ω s hs1 x
  · intro a b hab
    exact ⟨0, by simpa only [pow_zero, one_mul] using (Subtype.ext hab : a = b)⟩

def fieldEquiv (s : LocalGeometricFontaine.integerRing Ω) (hs0 : s ≠ 0) (hs1 : ‖(s : Ω)‖ < 1) :
    Localization.Away s ≃ₐ[LocalGeometricFontaine.integerRing Ω] Ω := by
  letI := field_isLocalization Ω s hs0 hs1
  exact IsLocalization.algEquiv (Submonoid.powers s) _ _

theorem fieldEquiv_algebraMap (s : LocalGeometricFontaine.integerRing Ω)
    (hs0 : s ≠ 0) (hs1 : ‖(s : Ω)‖ < 1) (a : LocalGeometricFontaine.integerRing Ω) :
    fieldEquiv Ω s hs0 hs1 (algebraMap _ (Localization.Away s) a) = (a : Ω) :=
  (fieldEquiv Ω s hs0 hs1).commutes a

end
end JoshiTeich.Act1Scene1.NormedIntegerLocalization
