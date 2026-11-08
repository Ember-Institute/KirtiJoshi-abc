import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSeedTateFamily
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateFamilyQRootAdapter

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut
open JoshiTeich.Prologue
open NumberField WeierstrassCurve
open scoped Classical

universe u

noncomputable section

local instance (priority := 1100)
    {F Fbar : Type u} [Field F] [Field Fbar] [Algebra F Fbar]
    (K : IntermediateField F Fbar) : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-!
source-id: IUT-COR312-TATE-FAMILY-QROOT-ADAPTER
source: seed specialization of the existing Tate-family q-root adapter;
Joshi III `ss:theta-data-fixing2`, especially the following paragraph
"Existence of local torsion points of order 2 ell"; reference
`Concrete/ThetaLocalConstruct/Roots.lean` and `Concrete/Existence.lean`.
fidelity: derives a finite base q-pilot source and torsion-completion roots
from the same arithmetic seed, its admissible prime, and its derived Tate
family. No orbicurve, local-theta witness, or geometry producer is required.
boundary: Scene1/Derived; restricted to the supplied VBad. This does not
construct the remaining geometry, holomorphoid, or theta-volume source.
-/

/-- The supplied bad locus has finite support already at the arithmetic seed. -/
theorem badPlacesOver_finite (S : InitialThetaGeometrySeed AG TG) :
    (badPlacesOver S.F S.E S.VBad).Finite := by
  refine (multiplicativeReductionPlaces_finite S.E).subset ?_
  rintro w ⟨v, hv, hwv⟩
  exact S.global.bad_multiplicative v hv w hwv

/-- The base q-pilot source uses the seed's own admissible-prime parameter. -/
def baseQPilotSource (S : InitialThetaGeometrySeed AG TG) :
    IutBaseQPilotSource S.F S.prime.ℓ :=
  IutBaseQPilotSource.ofAdmissiblePrimeData S.prime.ℓ S.prime
    S.badPlacesOver_finite

/-- Every torsion-field place above the base source is in the seed's Tate locus. -/
theorem torsionQRootSource_badPlace
    (S : InitialThetaGeometrySeed AG TG)
    (w : iutBadPlacesOverFinset (k := S.F) (K := ↥S.prime.torsionField)
      S.baseQPilotSource.badPlaces S.baseQPilotSource.badPlaces_finite) :
    IsBadPlace S.E S.prime.torsionField S.VBad w.1 := by
  let B := S.baseQPilotSource
  have hbase : (IutTorsionQRootSource.basePlaceOf (B := B) w).1 ∈
      badPlacesOver S.F S.E S.VBad :=
    B.mem_badPlaces (IutTorsionQRootSource.basePlaceOf (B := B) w)
  rcases hbase with ⟨v, hv, hvbase⟩
  let : Algebra ↥(fieldOfModuli S.F S.E) ↥S.prime.torsionField :=
    (fieldOfModuli S.F S.E).instAlgebraSubtypeMem
  have hfieldHom :
      algebraMap ↥(fieldOfModuli S.F S.E) ↥S.prime.torsionField =
        (algebraMap S.F ↥S.prime.torsionField).comp
          (algebraMap ↥(fieldOfModuli S.F S.E) S.F) :=
    RingHom.ext (fun _ => rfl)
  let : IsScalarTower ↥(fieldOfModuli S.F S.E) S.F ↥S.prime.torsionField :=
    IsScalarTower.of_algebraMap_eq' hfieldHom
  let : IsScalarTower (𝓞 ↥(fieldOfModuli S.F S.E)) (𝓞 S.F)
      (𝓞 ↥S.prime.torsionField) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hfieldHom x)
  have : w.1.maximalIdeal.asIdeal.LiesOver
      (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal :=
    IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w
  have : (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal.LiesOver
      v.maximalIdeal.asIdeal := hvbase
  exact ⟨v, hv, ⟨(Ideal.LiesOver.trans w.1.maximalIdeal.asIdeal
    (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal).over⟩⟩

private theorem tate_q_eq_baseQPilotSource
    (S : InitialThetaGeometrySeed AG TG)
    (w : iutBadPlacesOverFinset (k := S.F) (K := ↥S.prime.torsionField)
      S.baseQPilotSource.badPlaces S.baseQPilotSource.badPlaces_finite) :
    ((S.tate.S w.1 (S.torsionQRootSource_badPlace w)).t.q :
      w.1.maximalIdeal.adicCompletion ↥S.prime.torsionField) =
        iutEmbedCompletion
          (IutTorsionQRootSource.basePlaceOf_liesOver (B := S.baseQPilotSource) w)
          (S.baseQPilotSource.tateParameter
            (IutTorsionQRootSource.basePlaceOf (B := S.baseQPilotSource) w)) := by
  let B := S.baseQPilotSource
  let v := IutTorsionQRootSource.basePlaceOf (B := B) w
  exact S.tate_q_eq_admissiblePrime (S.torsionQRootSource_badPlace w)
    (B.mem_badPlaces v) (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w)

/-- Construct the roots before the missing orbicurve/local-theta producer. -/
def torsionQRootSource (S : InitialThetaGeometrySeed AG TG) :
    IutTorsionQRootSource S.F ↥S.prime.torsionField S.prime.ℓ
      S.baseQPilotSource := by
  let P := IutAdmissiblePrimeTorsionData.ofAdmissiblePrimeData
    S.prime S.isAlgClosure
  letI : IsAlgClosed S.Fbar := S.isAlgClosure.isAlgClosed
  have hsix : IutSixTorsionRational (F := S.F) (Fbar := S.Fbar) (E := S.E) := by
    have hcurve : Affine.baseChange S.E S.Fbar =
        (S.E.map (algebraMap S.F S.Fbar)).toAffine := rfl
    cases hcurve
    change ∀ Q ∈ iutTorsion
      ((S.E.map (algebraMap S.F S.Fbar)).toAffine.Point) 6,
      Q ∈ (iutWeierstrassPointMap (E := S.E) (algebraMap S.F S.Fbar)).range
    exact S.global.six_torsion_rational
  have hfield := IutAdmissiblePrimeTorsionData.torsionField_eq_admissiblePrime
    S.prime S.isAlgClosure
  have T : IutGlobalTorsionBasis
      (S.E.map (algebraMap S.F ↥S.prime.torsionField)).toAffine.Point S.prime.ℓ := by
    rw [← hfield]
    exact P.toGlobalTorsionBasis
  exact IutTorsionQRootSource.ofTateFamily S.baseQPilotSource T S.VBad S.tate
    (fun w => S.torsionQRootSource_badPlace w)
    hsix P.ell_pos P.ell_odd (fun w => S.tate_q_eq_baseQPilotSource w)

/-- The root from the same source is a root of the derived Tate parameter. -/
theorem torsionQRootSource_qroot_pow_eq_tate
    (S : InitialThetaGeometrySeed AG TG)
    (w : S.torsionQRootSource.badFinset) :
    S.torsionQRootSource.qroot w ^ (2 * S.prime.ℓ) =
      ((S.tate.S w.1 (S.torsionQRootSource_badPlace w)).t.q :
        w.1.maximalIdeal.adicCompletion ↥S.prime.torsionField) := by
  exact (S.torsionQRootSource.qroot_pow_eq w).trans
    (S.tate_q_eq_baseQPilotSource w).symm

end

end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
