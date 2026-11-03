import ArithmeticTeichmullerSpaces.Act1Scene1.PadicTiltField
import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichLocalization
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.Localization.Away.Basic

/-!
source-id: JT-SCENE1-STANDARD-PADIC-BOUNDED-WITT
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`.
fidelity: constructs W(O_F)[1/p,1/[t]] for the standard F=C_p^flat.
The nonzero contraction t is chosen from the original standard tilt.
All public declarations depend only on p and its primality instance.
boundary: this is an algebraic localization. The completed paper B and
its rho norms are not constructed here. Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicBoundedWittLocalization

noncomputable section
variable (p : ℕ) [Fact p.Prime]

/-- A nonzero contraction chosen in the standard tilt integer ring. -/
def contraction : PadicTiltField.Integers p :=
  ⟨Classical.choose (PadicTiltField.exists_contracting p),
    (LocalGeometricFontaine.mem_integerRing _ _).mpr
      (le_of_lt (Classical.choose_spec (PadicTiltField.exists_contracting p)).2)⟩

theorem contraction_ne_zero : contraction p ≠ 0 := by
  have hpos : 0 < ‖contraction p‖ :=
    (Classical.choose_spec (PadicTiltField.exists_contracting p)).1
  exact norm_pos_iff.mp hpos

theorem contraction_norm_lt_one : ‖contraction p‖ < 1 :=
  (Classical.choose_spec (PadicTiltField.exists_contracting p)).2

abbrev Ainf := WittVector p (PadicTiltField.Integers p)

def teich : Ainf p := WittVector.teichmuller p (contraction p)

abbrev denominator := WittPrimeTeichLocalization.denominator p (contraction p)

/-- The algebraic localization that inverts p and the chosen Teichmuller lift. -/
abbrev Ring := WittPrimeTeichLocalization.Ring p (contraction p)

def inclusion : Ainf p →+* Ring p := algebraMap _ _

theorem prime_isUnit : IsUnit (inclusion p p) := by
  apply isUnit_of_mul_isUnit_left (y := inclusion p (teich p))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (denominator p)

theorem teich_isUnit : IsUnit (inclusion p (teich p)) := by
  apply isUnit_of_mul_isUnit_right (x := inclusion p p)
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (denominator p)

end
end JoshiTeich.Act1Scene1.PadicBoundedWittLocalization
