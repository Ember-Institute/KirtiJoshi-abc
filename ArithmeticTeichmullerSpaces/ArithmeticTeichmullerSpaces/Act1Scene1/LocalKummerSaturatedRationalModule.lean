import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedLogEquivalence
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
source-id: JT-SCENE1-SATURATED-KUMMER-RATIONAL-MODULE
source: the standard rational H1 additive group and the proved saturated
ordinary-log equivalence; Joshi III 3212--3226.
fidelity: restricts the existing Q_p action on standard H1 to rational scalars,
proves the saturated image is exactly the range of a rational-linear embedding,
and identifies its linear logarithm with the original ordinary image log.
No scalar action is transported from the coordinate. Q_p scalar closure,
H1_e/BK and topological comparison remain open.
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
local instance rationalH1Module : Module ℚ H := Module.compHom H (algebraMap ℚ ℚ_[p])

/-- The ordinary inverse log followed by inclusion in the existing H1 module. -/
def saturatedExpToRationalH1 : k →ₗ[ℚ] H :=
  (((saturatedKummerImage (k := k) (Ω := Ω) p).subtype).comp
    (saturatedExp p hpk)).toRatLinearMap

theorem saturatedExpToRationalH1_injective :
    Function.Injective (saturatedExpToRationalH1 (Ω := Ω) p hpk) := by
  intro x y h
  exact (saturatedLogEquiv p hpk).symm.injective (Subtype.ext h)

def saturatedKummerRatSubmodule : Submodule ℚ H :=
  (saturatedExpToRationalH1 (Ω := Ω) p hpk).range

/-- Equality of carriers proves closure under the ambient rational action. -/
theorem mem_saturatedKummerRatSubmodule_iff (x : H) :
    x ∈ saturatedKummerRatSubmodule p hpk ↔ x ∈ saturatedKummerImage p := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (saturatedExp (Ω := Ω) p hpk y).2
  · intro hx
    refine ⟨saturatedImageLog p hpk ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (saturatedExp_saturatedImageLog p hpk ⟨x, hx⟩)

include hpk in
theorem ratCast_smul_mem_saturatedKummerImage (r : ℚ) {x : H}
    (hx : x ∈ saturatedKummerImage p) :
    (r : ℚ_[p]) • x ∈ saturatedKummerImage p := by
  have hm := (saturatedKummerRatSubmodule (Ω := Ω) p hpk).smul_mem r
    ((mem_saturatedKummerRatSubmodule_iff p hpk x).mpr hx)
  exact (mem_saturatedKummerRatSubmodule_iff p hpk _).mp hm

/-- The scalar action on the source is the restriction of standard H1 scalars. -/
def saturatedRatLogEquiv : saturatedKummerRatSubmodule (Ω := Ω) p hpk ≃ₗ[ℚ] k :=
  (LinearEquiv.ofInjective (saturatedExpToRationalH1 p hpk)
    (saturatedExpToRationalH1_injective p hpk)).symm

theorem saturatedRatLogEquiv_eq_imageLog
    (x : saturatedKummerRatSubmodule (Ω := Ω) p hpk) :
    saturatedRatLogEquiv p hpk x = saturatedImageLog p hpk
      ⟨x.1, (mem_saturatedKummerRatSubmodule_iff p hpk x.1).mp x.2⟩ := by
  have h := congrArg Subtype.val
    ((LinearEquiv.ofInjective (saturatedExpToRationalH1 p hpk)
      (saturatedExpToRationalH1_injective p hpk)).apply_symm_apply x)
  change (saturatedExp (k := k) (Ω := Ω) p hpk (saturatedRatLogEquiv p hpk x)).1 = x.1 at h
  calc
    _ = saturatedImageLog p hpk (saturatedExp p hpk (saturatedRatLogEquiv p hpk x)) :=
      (saturatedImageLog_saturatedExp p hpk _).symm
    _ = _ := congrArg (saturatedImageLog p hpk) (Subtype.ext h)

end
end JoshiTeich.Act1Scene1.LocalPadicLog
