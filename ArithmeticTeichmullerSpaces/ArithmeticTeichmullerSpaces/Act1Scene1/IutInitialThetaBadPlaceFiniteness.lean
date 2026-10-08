import ArithmeticTeichmullerSpaces.Act1Scene1.IutAdmissiblePrimeSource
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlaceUnder

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve
open scoped NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-BAD-FINITENESS
source: `iut`: `refer/iut/Iut/Concrete/CurveArithmeticProved.lean`,
`EllipticCurveData.badAll_finite`; `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`,
`badPlacesOver` and `IsInitialThetaGlobalData.bad_multiplicative`.
fidelity: derives finiteness of the actual `InitialThetaData` bad-place carrier
from finite multiplicative support of the curve's `j`-invariant, and uses that
proof to construct its base q-pilot source.
boundary: Scene1/Derived
-/

private theorem iut_norm_emb_le_one_iff
    {F : Type u} [Field F] [NumberField F] (w : NumberField.FinitePlace F) (y : F) :
    ‖(NumberField.FinitePlace.embedding w.maximalIdeal y :
      JoshiTeich.ReferenceIut.localCompletion w)‖ ≤ 1 ↔
      w.maximalIdeal.valuation F y ≤ 1 := by
  rw [JoshiTeich.ReferenceIut.norm_le_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation']

private theorem iut_multiplicative_places_finite
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    {w : NumberField.FinitePlace D.F | JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E w}.Finite := by
  by_cases hj : D.E.j = 0
  · refine Set.Finite.subset Set.finite_empty ?_
    intro w hw
    have hval := JoshiTeich.ReferenceIut.one_lt_valuation_j_of_mult D.E w hw
    rw [hj, map_zero] at hval
    exact absurd hval (not_lt.2 zero_le_one)
  · refine (NumberField.FinitePlace.hasFiniteMulSupport hj).subset ?_
    intro w hw
    rw [Function.mem_mulSupport, ← NumberField.FinitePlace.norm_embedding_eq]
    intro h
    exact absurd ((iut_norm_emb_le_one_iff w D.E.j).1 h.le)
      (not_le.2 (JoshiTeich.ReferenceIut.one_lt_valuation_j_of_mult D.E w hw))

/-- The actual IUT bad-place carrier is finite, derived from its multiplicative
reduction source rather than supplied as a separate finiteness input. -/
theorem iutInitialThetaBadPlacesOver_finite
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad).Finite := by
  refine (iut_multiplicative_places_finite D).subset ?_
  intro w hw
  rcases hw with ⟨v, hv, hwv⟩
  exact D.global.bad_multiplicative v hv w hwv

/-- Build the base q-pilot source from actual `InitialThetaData`; finiteness of
`badPlacesOver` is proved from the curve's `j`-support. -/
noncomputable def IutBaseQPilotSource.ofInitialThetaData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutBaseQPilotSource D.F D.prime.ℓ :=
  IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime
    (iutInitialThetaBadPlacesOver_finite D)

end

end JoshiTeich.Act1Scene1
