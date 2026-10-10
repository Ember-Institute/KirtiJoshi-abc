import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadSupport

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-FULL-SUPPORT-VBAD-COVERAGE
source: `IutInitialThetaBadSupport.lean`, including the one-sided
`badPlacesOver` inclusion and the definition of `IutOddMultiplicativeSupport`;
`refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`, `badPlacesOver`.
fidelity: records the exact reverse-coverage obligation needed to identify the
complete odd multiplicative support with the q-pilot carrier selected by
`InitialThetaData.VBad`. The reverse condition is left as an explicit source
input and is not inferred from the existing one-sided `VBad` fields.
boundary: Scene1/Derived
-/

/-! The full odd support equals the actual q-pilot carrier exactly when every
full-support place lies over a selected `VBad` place. -/
theorem iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_VBad_iff
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutOddMultiplicativeSupport D =
        JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad ↔
      ∀ w : NumberField.FinitePlace D.F,
        w ∈ IutOddMultiplicativeSupport D →
          ∃ v : NumberField.FinitePlace
              (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E),
            v ∈ D.VBad ∧
              JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v := by
  constructor
  · intro hEq w hw
    have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
      rw [← hEq]
      exact hw
    exact hwBad
  · intro hCoverage
    apply Set.Subset.antisymm
    · intro w hw
      exact hCoverage w hw
    · exact iutBadPlacesOver_subset_oddMultiplicativeSupport D

/-! The reverse-coverage condition can also be stated as a support inclusion;
this form is convenient when the source supplies a set equality or subset. -/
theorem iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_VBad_iff_subset
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutOddMultiplicativeSupport D =
        JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad ↔
      IutOddMultiplicativeSupport D ⊆
        JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
  constructor
  · intro hEq
    intro w hw
    rw [← hEq]
    exact hw
  · intro hSubset
    apply Set.Subset.antisymm
    · exact hSubset
    · exact iutBadPlacesOver_subset_oddMultiplicativeSupport D

end

end JoshiTeich.Act1Scene1
