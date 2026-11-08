import ArithmeticTeichmullerSpaces.Act1Scene1.ProducerContracts
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaValuationSection
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateParameterCompletion

namespace JoshiTeich.Act1Scene1

open JoshiTeich.ReferenceIut
open NumberField WeierstrassCurve
open scoped Valued

universe u

noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-!
source-id: JT-SCENE1-SEED-TATE-FAMILY-20261108
source: Joshi III `ss:theta-data-fixing2` and
`pr:admissible-lifts-tate-params`; the local port of
`Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`; Tate-parameter `j` uniqueness.
fidelity: identifies the derived family parameter with the seed's admissible-
prime parameter at every pair of compatible bad places, including the actual
valuation-section choice.
boundary: Scene1/Derived. The result is limited to the seed's supplied `VBad`.
It does not construct `OrbicurveData`, `LocalThetaData`, or a geometry producer.
-/

/-- The Tate family derived from a seed has the admissible-prime q-parameter
after extension to any compatible torsion-field completion. -/
theorem InitialThetaGeometrySeed.tate_q_eq_admissiblePrime
    (S : InitialThetaGeometrySeed AG TG)
    {wK : FinitePlace ↥S.prime.torsionField}
    {wF : FinitePlace S.F}
    (hwK : IsBadPlace S.E S.prime.torsionField S.VBad wK)
    (hwF : wF ∈ badPlacesOver S.F S.E S.VBad)
    (hOver : Ideal.LiesOver wK.maximalIdeal.asIdeal wF.maximalIdeal.asIdeal) :
    ((S.tate.S wK hwK).t.q : localCompletion wK) =
      iutEmbedCompletion hOver ((S.prime.tate wF hwF).q : localCompletion wF) := by
  apply iutTateParameter_q_eq_of_tateJ_eq hOver
  rw [← iutTateJ_embed hOver, S.prime.tateJ_eq wF hwF,
    iutEmbedCompletion_embedding hOver, iutTateStructure_tateJ_eq,
    iutCurve_j_eq_div]
  simp only [curveKw, curveK, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ,
    map_div₀, map_pow]

/-- The section selected by the seed consumes the same q-parameter comparison. -/
theorem InitialThetaGeometrySeed.valuationSection_tate_q_eq_admissiblePrime
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    let wK := S.valuationSection.sectFin v
    let hwK : IsBadPlace S.E S.prime.torsionField S.VBad wK :=
      S.prime.sectFin_isBad S.tate hv
    let wF := S.valuationSection_contractedPlace v
    let hwF : wF ∈ badPlacesOver S.F S.E S.VBad :=
      ⟨v, hv, S.valuationSection_contractedPlace_liesOver v⟩
    let hOver : Ideal.LiesOver wK.maximalIdeal.asIdeal wF.maximalIdeal.asIdeal :=
      iutPlaceUnder_liesOver (F := S.F) (Kt := ↥S.prime.torsionField) wK
    ((S.tate.S wK hwK).t.q : localCompletion wK) =
      iutEmbedCompletion hOver ((S.prime.tate wF hwF).q : localCompletion wF) := by
  let wK := S.valuationSection.sectFin v
  let hwK : IsBadPlace S.E S.prime.torsionField S.VBad wK :=
    S.prime.sectFin_isBad S.tate hv
  let wF := S.valuationSection_contractedPlace v
  let hwF : wF ∈ badPlacesOver S.F S.E S.VBad :=
    ⟨v, hv, S.valuationSection_contractedPlace_liesOver v⟩
  let hOver : Ideal.LiesOver wK.maximalIdeal.asIdeal wF.maximalIdeal.asIdeal :=
    iutPlaceUnder_liesOver (F := S.F) (Kt := ↥S.prime.torsionField) wK
  change ((S.tate.S wK hwK).t.q : localCompletion wK) =
    iutEmbedCompletion hOver ((S.prime.tate wF hwF).q : localCompletion wF)
  exact S.tate_q_eq_admissiblePrime hwK hwF hOver

end

end JoshiTeich.Act1Scene1
