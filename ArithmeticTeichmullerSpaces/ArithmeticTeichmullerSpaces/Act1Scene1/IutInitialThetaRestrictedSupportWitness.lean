import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRestrictBadPlaces
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedSupportDefect

/-!
source-id: JT-SCENE1-INITIAL-THETA-RESTRICTED-SUPPORT-WITNESS
source: full InitialThetaData restriction and the exact omitted q-log criterion.
fidelity: given actual data with two distinct chosen bad places, constructs
actual data whose singleton bad support omits a proved odd multiplicative
place and has strictly positive omitted paper sum. This is a conditional
countermodel construction; existence of such starting data is not claimed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaRestriction
open JoshiTeich.Prologue NumberField
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem restrict_oddSupport (W : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)))
    (hW : W ⊆ D.VBad) (hne : W.Nonempty) :
    IutOddMultiplicativeModSupport (restrict D W hW hne) = IutOddMultiplicativeModSupport D := rfl

def singleton (v : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (hv : v ∈ D.VBad) :
    JoshiTeich.ReferenceIut.InitialThetaData AG TG :=
  restrict D {v} (Set.singleton_subset_iff.mpr hv) (Set.singleton_nonempty v)

theorem singleton_missing_place
    (v w : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ D.VBad) (hw : w ∈ D.VBad) (hvw : w ≠ v) :
    w ∈ IutOddMultiplicativeModSupport (singleton D v hv) ∧ w ∉ (singleton D v hv).VBad := by
  constructor
  · exact iutInitialThetaVBad_subset_oddMultiplicativeModSupport D hw
  · exact hvw

theorem singleton_not_full_coverage
    (v w : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ D.VBad) (hw : w ∈ D.VBad) (hvw : w ≠ v) :
    iutInitialThetaVBadModuliFinset (singleton D v hv) ≠
      iutInitialThetaOddModSupportFinset (singleton D v hv) := by
  obtain ⟨hfull, hmissing⟩ := singleton_missing_place D v w hv hw hvw
  rw [iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd] at hfull
  intro heq
  have hm : w ∈ iutInitialThetaOddModSupportFinset (singleton D v hv) :=
    (iutInitialThetaOddModSupport_finite (singleton D v hv)).mem_toFinset.mpr hfull
  rw [← heq] at hm
  exact hmissing ((mem_iutInitialThetaVBadModuliFinset_iff (singleton D v hv) w).mp hm)

theorem singleton_omittedPaperSum_pos
    (v w : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ D.VBad) (hw : w ∈ D.VBad) (hvw : w ≠ v) :
    0 < VBadSelectedPaper.omittedPaperSum (singleton D v hv) := by
  have hne : VBadSelectedPaper.omittedPaperSum (singleton D v hv) ≠ 0 :=
    fun h => singleton_not_full_coverage D v w hv hw hvw
      ((VBadSelectedPaper.omittedPaperSum_eq_zero_iff_coverage (singleton D v hv)).mp h)
  exact lt_of_le_of_ne (VBadSelectedPaper.omittedPaperSum_nonneg (singleton D v hv)) hne.symm

theorem exists_restricted_data_with_missing_support
    (v w : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ D.VBad) (hw : w ∈ D.VBad) (hvw : w ≠ v) :
    ∃ E : JoshiTeich.ReferenceIut.InitialThetaData AG TG,
      iutInitialThetaVBadModuliFinset E ≠ iutInitialThetaOddModSupportFinset E ∧
        0 < VBadSelectedPaper.omittedPaperSum E :=
  ⟨singleton D v hv, singleton_not_full_coverage D v w hv hw hvw,
    singleton_omittedPaperSum_pos D v w hv hw hvw⟩

end
end JoshiTeich.Act1Scene1.InitialThetaRestriction
