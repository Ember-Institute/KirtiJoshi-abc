import ArithmeticTeichmullerSpaces.Act1Scene1.IutQSourceContract
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.AdmissiblePrime
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped NumberField

universe u

/-!
source-id: IUT-COR312-INITIAL-THETA-BASE-QPILOT
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`InitialThetaData.prime`; `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`AdmissiblePrimeData.tate`.
fidelity: constructs the base-field q-pilot carrier, Tate parameters and
arithmetic weights from an actual admissible-prime datum.
boundary: Scene1/Derived
-/

/-- The actual IUT base-field q-pilot carrier and Tate parameters. -/
noncomputable def IutBaseQPilotSource.ofAdmissiblePrimeData
    {F : Type u} [Field F] [NumberField F]
    {E : WeierstrassCurve F} [E.IsElliptic]
    {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
    {VBad : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E))}
    (ell : ℕ) (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad)
    (hBadFinite : (JoshiTeich.ReferenceIut.badPlacesOver F E VBad).Finite) :
    IutBaseQPilotSource F ell := by
  refine
    { badPlaces := JoshiTeich.ReferenceIut.badPlacesOver F E VBad
      badFinset := hBadFinite.toFinset
      badFinset_spec := hBadFinite.coe_toFinset
      weight := Arithmetic.qPilotWeight
      weight_eq_qPilotWeight := fun _ => rfl
      tateParameter := fun w =>
        (P.tate w.1 (hBadFinite.mem_toFinset.mp w.2)).q
      tateParameter_ne_zero := ?_
      tateParameter_norm_lt_one := ?_ }
  · intro w
    exact (P.tate w.1 (hBadFinite.mem_toFinset.mp w.2)).q.ne_zero
  · intro w
    exact (P.tate w.1 (hBadFinite.mem_toFinset.mp w.2)).norm_lt_one

end JoshiTeich.Act1Scene1
