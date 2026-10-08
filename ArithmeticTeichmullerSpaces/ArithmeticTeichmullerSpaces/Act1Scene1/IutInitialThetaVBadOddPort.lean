import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadSupport

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-VBAD-ODD-SUPPORT-PORT
source: `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean`,
`EllipticCurveData.VBadOdd`.
fidelity: identifies the project's canonical odd multiplicative support with
the exact local port of the reference project's `VBadOdd` definition, then
proves the selected `InitialThetaData.VBad` is contained in it. It does not
identify the selected set with the complete support or with paper representatives.
boundary: Scene1/Derived
-/

/-- The `EllipticCurveData.VBadOdd` support, ported from `iut`. -/
def iutVBadOddModSupportPort
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace ↥(Iut.fieldOfModuli D.F D.E)) :=
  {v | Arithmetic.residueChar v ≠ 2 ∧
    (∃ w : NumberField.FinitePlace D.F, Iut.FinitePlace.LiesOver w v) ∧
    ∀ w : NumberField.FinitePlace D.F, Iut.FinitePlace.LiesOver w v →
      Iut.HasMultiplicativeReductionAt D.E w}

theorem iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG) :
    IutOddMultiplicativeModSupport D =
      iutVBadOddModSupportPort D := by
  ext v
  simp only [IutOddMultiplicativeModSupport,
    iutVBadOddModSupportPort, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hodd, hex, hmult⟩
    refine ⟨?_, hex, hmult⟩
    intro htwo
    rcases hodd with ⟨n, hn⟩
    rw [htwo] at hn
    omega
  · rintro ⟨hne, hex, hmult⟩
    refine ⟨?_, hex, hmult⟩
    have hp : (Arithmetic.residueChar v).Prime := Arithmetic.residueChar_prime v
    rcases hp.eq_two_or_odd' with htwo | hodd
    · exact (hne htwo).elim
    · exact hodd

theorem iutInitialThetaVBad_subset_VBadOdd
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG) :
    D.VBad ⊆ iutVBadOddModSupportPort D := by
  rw [← iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
  exact iutInitialThetaVBad_subset_oddMultiplicativeModSupport D

end

end JoshiTeich.Act1Scene1
