import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootAccounting
import Iut.Cor312.ThetaData.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped NumberField

universe u

/-!
source-id: IUT-COR312-INITIAL-THETA-BAD-SUPPORT
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`,
`badPlacesOver`, `IsInitialThetaGlobalData.bad_odd`, and
`IsInitialThetaGlobalData.bad_multiplicative`.
fidelity: proves that every place in the actual IUT q-pilot bad-place carrier
has odd residue characteristic and multiplicative reduction over the IUT base
field. This is a one-way support property; it does not identify the carrier
with the paper's `V_p^oss`.
boundary: Scene1/Derived
-/

noncomputable section

/-- The odd-characteristic multiplicative places of the IUT base curve. -/
def IutOddMultiplicativeSupport
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG) : Set (NumberField.FinitePlace D.F) :=
  {w | Odd (Arithmetic.residueChar w) ∧ Iut.HasMultiplicativeReductionAt D.E w}

/-- The actual IUT q-pilot support lies in the odd multiplicative support. -/
theorem iutBadPlacesOver_subset_oddMultiplicativeSupport
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG) :
    Iut.badPlacesOver D.F D.E D.VBad ⊆ IutOddMultiplicativeSupport D := by
  intro w hw
  rcases hw with ⟨v, hv, hwv⟩
  refine ⟨?_, D.global.bad_multiplicative v hv w hwv⟩
  rw [Arithmetic.residueChar_eq_of_liesOver hwv]
  exact D.global.bad_odd v hv

end

end JoshiTeich.Act1Scene1
