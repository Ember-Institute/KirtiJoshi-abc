import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRoot

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open IsDedekindDomain.HeightOneSpectrum
open NumberField TateCurvesTheta
open scoped NumberField Valued

universe u

/-!
source-id: IUT-COR312-ODD-SUPPORT-TATE-BASE-CHANGE
source: `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean` (`VBadOdd`),
`Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`, and completion transport from
`Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean` and `TateCompat.lean`,
ported in `IutTateParameterCompletion.lean`; `TateParameter.tateJ_injective`
is from `tate-curves-theta` at fixed commit
`ca6c2279d3cea0690cdb01328e727118d5485d68`,
`TateCurvesTheta/QParameter/JParametrization.lean`.
fidelity: proves that the locally constructed Tate parameter at any place of
the original field above a moduli place is the completion image of the moduli
field Tate parameter. This is a local compatibility result; it does not identify
global q-sums or the IUT-selected `VBad` with the full support.
boundary: Scene1/Derived
-/

private theorem iutInitialThetaOddSupport_mem_of_liesOver
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D)
    (w : NumberField.FinitePlace D.F)
    (hwv : JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v) :
    w ∈ IutOddMultiplicativeSupport D := by
  refine ⟨?_, hv.2.2 w hwv⟩
  have hodd : Odd (Arithmetic.residueChar v) := by
    have hp := Arithmetic.residueChar_prime v
    rcases hp.eq_two_or_odd' with htwo | hodd
    · exact (hv.1 htwo).elim
    · exact hodd
  rw [Arithmetic.residueChar_eq_of_liesOver hwv]
  exact hodd

theorem iutInitialThetaOddSupportBaseTateParameter_q_eq_of_liesOver
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D)
    (w : NumberField.FinitePlace D.F)
    (hwv : JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v) :
    (iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w
      (iutInitialThetaOddSupport_mem_of_liesOver D v hv w hwv)).q =
      iutEmbedCompletion hwv
        ((iutInitialThetaOddSupportBaseTateParameter D v hv).q) := by
  let t := iutInitialThetaOddSupportBaseTateParameter D v hv
  have hwSupport : w ∈ IutOddMultiplicativeSupport D :=
    iutInitialThetaOddSupport_mem_of_liesOver D v hv w hwv
  let s := iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w
    hwSupport
  have hmoduliJ :
      algebraMap (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) D.F
        (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩) = D.E.j := rfl
  have hJ : (iutEmbedTateParameter hwv t).tateJ = s.tateJ := by
    calc
      (iutEmbedTateParameter hwv t).tateJ = iutEmbedCompletion hwv t.tateJ :=
        (iutTateJ_embed hwv t).symm
      _ = NumberField.FinitePlace.embedding w.maximalIdeal D.E.j := by
        rw [iutInitialThetaOddSupportBaseTateParameter_tateJ_eq D v hv,
          iutEmbedCompletion_embedding hwv]
        change NumberField.FinitePlace.embedding w.maximalIdeal
          (algebraMap (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) D.F
            (⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩)) = _
        rw [hmoduliJ]
      _ = s.tateJ :=
        (iutInitialThetaOddSupportBaseTateParameterAtCurvePlace_tateJ_eq D w
          hwSupport).symm
  simpa [t, s] using iutTateParameter_q_eq_of_tateJ_eq hwv t s hJ

end JoshiTeich.Act1Scene1
