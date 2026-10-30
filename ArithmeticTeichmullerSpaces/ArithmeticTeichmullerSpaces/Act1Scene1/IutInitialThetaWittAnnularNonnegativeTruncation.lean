import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNegativeTruncation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAnnularFiniteCoordinateDensity

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ANNULAR-NONNEGATIVE-TRUNCATION
source: Joshi II `se:ff-rings`, annular rho norms and the bounded Witt
source preceding `pr:teichmuller-lift-A`.
fidelity: an original bounded source element that is unit-bounded at
every annular radius admits one no-negative-p-power source approximation.
The approximation remains unit-bounded at every annular radius and its
error is bounded by the base-radius ratio rho/r. This is the exact
annular form of the proved negative-head estimate, with no integral
representative assumption.
Original proof; no reference code copied.
boundary: Scene1/Derived; the hypothesis is an actual source element
with all annular unit bounds. Annular density alone does not provide
this hypothesis, and annular Ainf representation remains open.
Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAnnularNonnegativeTruncation

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion
open InitialThetaWittAnnularExponential
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius

theorem exists_annular_nonnegative_source
    (ρ : Radius) (y : InitialThetaBoundedWittLocalization.Ring D w)
    (hy : ∀ s : AnnularRadius ρ,
      InitialThetaWittRhoNorm.realValue D w s.val.val y ≤ 1) :
    ∃ a : InitialThetaBoundedWittLocalization.Ring D w, ∃ b : FieldWitt D w,
      toAmbient D w a = algebraMap (FieldWitt D w) (Ambient D w) b ∧
      (∀ s : AnnularRadius ρ,
        InitialThetaWittRhoNorm.realValue D w s.val.val (y - a) ≤
          ρ.val.toReal / s.val.val.toReal) ∧
      (∀ s : AnnularRadius ρ,
        InitialThetaWittRhoNorm.realValue D w s.val.val a ≤ 1) := by
  obtain ⟨a, b, hab, ha⟩ := InitialThetaWittNegativeTruncation.exists_nonnegative_approximation D w y
  refine ⟨a, b, hab, ?_, ?_⟩
  · intro s
    have hs : ρ.val ≤ s.val.val := s.property
    have h := ha ρ s hs
    have hρ : InitialThetaWittRhoNorm.realValue D w ρ.val y ≤ 1 := hy ⟨ρ, le_rfl⟩
    exact (h.trans (mul_le_of_le_one_right
      (div_nonneg (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)) hρ))
  · intro s
    have hs : ρ.val ≤ s.val.val := s.property
    have herror := ha ρ s hs
    have hρ : InitialThetaWittRhoNorm.realValue D w ρ.val y ≤ 1 := hy ⟨ρ, le_rfl⟩
    have hρs : 0 ≤ ρ.val.toReal / s.val.val.toReal := by positivity
    have hle : ρ.val.toReal / s.val.val.toReal ≤ 1 := by
      apply (div_le_one (ENNReal.toReal_pos s.val.property.1.ne'
        (s.val.property.2.trans ENNReal.one_lt_top).ne)).mpr
      exact (ENNReal.toReal_le_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne
        (s.val.property.2.trans ENNReal.one_lt_top).ne).mpr hs
    have hsum := InitialThetaWittRhoNorm.realValue_add_le_max D w s.val.val
      s.val.property.1.ne' s.val.property.2.le y (-(y - a))
    rw [show y + -(y - a) = a by ring,
      InitialThetaWittRhoNorm.realValue_neg D w s.val.val s.val.property.1.ne' s.val.property.2.le] at hsum
    exact hsum.trans (max_le (hy s)
      (herror.trans ((mul_le_of_le_one_right hρs hρ).trans hle)))

end
end JoshiTeich.Act1Scene1.InitialThetaWittAnnularNonnegativeTruncation
