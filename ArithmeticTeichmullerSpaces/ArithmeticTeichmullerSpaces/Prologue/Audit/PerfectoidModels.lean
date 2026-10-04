import ArithmeticTeichmullerSpaces.Prologue.Perfectoid
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.Topology

namespace JoshiTeich.Prologue.Audit

open Ideal PreTilt WittVector
open JoshiTeich.Prologue.Perfectoid

instance padicTwo_not_unit : Fact (¬ IsUnit (2 : ℤ_[2])) := by
  exact ⟨by
    simpa [nonunits] using (PadicInt.p_nonunit (p := 2))⟩

noncomputable instance padicTwo_is_adic_complete :
    IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] := by
  have h : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[2]) ℤ_[2] := inferInstance
  rw [PadicInt.maximalIdeal_eq_span_p (p := 2)] at h
  exact h
/-!
Concrete perfectoid audit models.  The production maps are mathlib's
`PreTilt.untilt` and Fontaine `fontaineTheta`; the zero functions below are
audit-only countermodels for the laws, not replacement carrier definitions.
-/

noncomputable def padicTwoUntilt :
    PreTilt ℤ_[2] 2 → ℤ_[2] :=
  @untiltMap ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
    padicTwo_is_adic_complete

noncomputable def padicTwoTheta :
    WittVector 2 (PreTilt ℤ_[2] 2) → ℤ_[2] :=
  @thetaMap ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
    padicTwo_is_adic_complete

noncomputable def padicTwoPerfectoidData :
    @PerfectoidData ℤ_[2] inferInstance 2 := {
  untilt := padicTwoUntilt
  theta := padicTwoTheta
}

theorem padicTwo_untilting_model :
    @UntiltingLaws ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
      padicTwoUntilt := by
  exact @canonicalUntiltingLaws ℤ_[2] inferInstance 2 inferInstance
    padicTwo_not_unit padicTwo_is_adic_complete

theorem padicTwo_theta_model :
    @FontaineThetaLaws ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
      padicTwoUntilt padicTwoTheta := by
  exact @canonicalFontaineThetaLaws ℤ_[2] inferInstance 2 inferInstance
    padicTwo_not_unit padicTwo_is_adic_complete

theorem padicTwo_perfectoid_model :
    @PerfectoidLaws ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
      padicTwoPerfectoidData := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := padicTwo_not_unit
  exact ⟨padicTwo_untilting_model, padicTwo_theta_model⟩

theorem padicTwo_parameter_nontrivial : (2 : ℕ) ≠ 1 := by norm_num

noncomputable def zeroUntilt : PreTilt ℤ_[2] 2 → ℤ_[2] := fun _ => 0

theorem zeroUntilt_violates_laws :
    ¬ @UntiltingLaws ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
      zeroUntilt := by
  intro h
  have hone := @UntiltingLaws.one ℤ_[2] inferInstance 2 inferInstance
    padicTwo_not_unit zeroUntilt h
  norm_num [zeroUntilt] at hone

noncomputable def zeroTheta : WittVector 2 (PreTilt ℤ_[2] 2) → ℤ_[2] := fun _ => 0

noncomputable def zeroPerfectoidData :
    @PerfectoidData ℤ_[2] inferInstance 2 := {
  untilt := zeroUntilt
  theta := zeroTheta
}

theorem zeroTheta_violates_laws :
    ¬ @FontaineThetaLaws ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
      padicTwoUntilt zeroTheta := by
  intro h
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := padicTwo_not_unit
  have hone := @FontaineThetaLaws.teichmuller ℤ_[2] inferInstance 2
    inferInstance padicTwo_not_unit padicTwoUntilt zeroTheta h
    (1 : PreTilt ℤ_[2] 2)
  simp [zeroTheta, padicTwoUntilt] at hone

theorem zeroPerfectoidData_violates_laws :
    ¬ @PerfectoidLaws ℤ_[2] inferInstance 2 inferInstance padicTwo_not_unit
      zeroPerfectoidData := by
  letI : Fact (¬ IsUnit (2 : ℤ_[2])) := padicTwo_not_unit
  intro h
  exact zeroUntilt_violates_laws h.untilting

end JoshiTeich.Prologue.Audit
