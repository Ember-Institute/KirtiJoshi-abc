import ArithmeticTeichmullerSpaces.Act1Scene1.IutTorsionRationality
import Iut.Cor312.ThetaData.Basic
import Iut.Cor312.ThetaData.TateFamily

/-!
source-id: IUT-COR312-TATE-FAMILY-QROOT-ADAPTER
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/TateStructure.lean` and
`refer/iut/Iut/Cor312/ThetaData/TateFamily.lean`.
fidelity: the actual IUT Tate parameter and uniformization is projected into the
group-theoretic quotient interface used by the q-root assembler. The
`InitialThetaData` constructor derives the bad-place certificate, torsion basis,
six-torsion condition, and positive odd prime from its actual fields. Comparison
with the base completion parameter remains explicit.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve
open NumberField
open scoped Classical Valued

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosed Fbar]
variable {Kt : IntermediateField F Fbar} [NumberField Kt]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {ell : ℕ}

local instance (priority := 1100) instDecidableEqKt : DecidableEq ↥Kt :=
  fun a b => Classical.propDecidable (a = b)

/-- Project the actual IUT Tate structure into the quotient-uniformization
interface used by the q-root argument. -/
def IutTateQuotientUniformization.ofTateStructure
    {K : Type u} [Field K]
    [Valued K (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))]
    [CompleteSpace K]
    {E : WeierstrassCurve K} (S : Iut.TateStructure E) :
    IutTateQuotientUniformization K E.toAffine.Point :=
  { q := S.t.q
    q_norm_lt_one := S.t.norm_lt_one
    iso := S.iso }

/-- Assemble the q-root source from the actual IUT Tate family. The proof that each
torsion-field place belongs to the IUT bad locus and the comparison of its Tate
parameter with the base completion parameter are retained as explicit inputs. -/
noncomputable def IutTorsionQRootSource.ofTateFamily
    (B : IutBaseQPilotSource F ell)
    (T : IutGlobalTorsionBasis (E.map (algebraMap F ↥Kt)).toAffine.Point ell)
    (VBad : Set (NumberField.FinitePlace ↥(Iut.fieldOfModuli F E)))
    (TF : Iut.TateFamily E Kt ell VBad)
    (hBad : ∀ w : iutBadPlacesOverFinset (k := F) (K := ↥Kt)
      B.badPlaces B.badPlaces_finite,
      Iut.IsBadPlace E Kt VBad w.1)
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E))
    (hEll : 0 < ell) (hodd : Odd ell)
    (hq : ∀ w : iutBadPlacesOverFinset (k := F) (K := ↥Kt)
      B.badPlaces B.badPlaces_finite,
      ((TF.S w.1 (hBad w)).t.q : w.1.maximalIdeal.adicCompletion ↥Kt) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) :
    IutTorsionQRootSource F ↥Kt ell B := by
  exact IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofWeierstrassTorsion
    B T
    (fun w => IutTateQuotientUniformization.ofTateStructure (TF.S w.1 (hBad w)))
    hsix hEll hodd hq

/-- Derive the local bad-place condition from the actual initial Theta-data carrier and
the base q-pilot carrier equality. -/
theorem iutInitialThetaTateFamily_badPlace
    {AG : Iut.AnabelianGeometry.{u}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (B : IutBaseQPilotSource D.F D.prime.ℓ)
    (hPlaces : B.badPlaces = Iut.badPlacesOver D.F D.E D.VBad)
    (w : iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      B.badPlaces B.badPlaces_finite) :
    Iut.IsBadPlace D.E D.prime.torsionField D.VBad w.1 := by
  have hbase : (IutTorsionQRootSource.basePlaceOf (B := B) w).1 ∈ B.badPlaces :=
    IutBaseQPilotSource.mem_badPlaces B
      (IutTorsionQRootSource.basePlaceOf (B := B) w)
  rw [hPlaces] at hbase
  rcases hbase with ⟨v, hv, hvbase⟩
  letI : Algebra ↥(Iut.fieldOfModuli D.F D.E) ↥D.prime.torsionField :=
    (Iut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hfieldMap (x : ↥(Iut.fieldOfModuli D.F D.E)) :
      algebraMap ↥(Iut.fieldOfModuli D.F D.E) ↥D.prime.torsionField x =
        algebraMap D.F ↥D.prime.torsionField
          (algebraMap ↥(Iut.fieldOfModuli D.F D.E) D.F x) := by
    rfl
  have hfieldHom :
      algebraMap ↥(Iut.fieldOfModuli D.F D.E) ↥D.prime.torsionField =
        (algebraMap D.F ↥D.prime.torsionField).comp
          (algebraMap ↥(Iut.fieldOfModuli D.F D.E) D.F) :=
    RingHom.ext hfieldMap
  letI : IsScalarTower ↥(Iut.fieldOfModuli D.F D.E) D.F
      ↥D.prime.torsionField :=
    IsScalarTower.of_algebraMap_eq' hfieldHom
  letI : IsScalarTower (𝓞 ↥(Iut.fieldOfModuli D.F D.E)) (𝓞 D.F)
      (𝓞 ↥D.prime.torsionField) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hfieldHom x)
  haveI : w.1.maximalIdeal.asIdeal.LiesOver
      (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal :=
    IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w
  haveI : (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal.LiesOver
      v.maximalIdeal.asIdeal := hvbase
  exact ⟨v, hv, ⟨(Ideal.LiesOver.trans w.1.maximalIdeal.asIdeal
    (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal).over⟩⟩

/-- Assemble q-root data from the real `InitialThetaData` and `TateFamily` fields.
The equality between each local Tate parameter and the base-completion parameter remains
an explicit source condition. -/
noncomputable def IutTorsionQRootSource.ofInitialThetaData
    {AG : Iut.AnabelianGeometry.{u}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (B : IutBaseQPilotSource D.F D.prime.ℓ)
    (hPlaces : B.badPlaces = Iut.badPlacesOver D.F D.E D.VBad)
    (hq : ∀ w : iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      B.badPlaces B.badPlaces_finite,
      ((D.tate.S w.1 (iutInitialThetaTateFamily_badPlace D B hPlaces w)).t.q :
        w.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) =
        iutEmbedCompletion (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (IutTorsionQRootSource.basePlaceOf (B := B) w))) :
    IutTorsionQRootSource D.F ↥D.prime.torsionField D.prime.ℓ B := by
  let P := IutAdmissiblePrimeTorsionData.ofAdmissiblePrimeData
    D.prime D.isAlgClosure
  letI : IsAlgClosed D.Fbar := D.isAlgClosure.isAlgClosed
  have hsix : IutSixTorsionRational (F := D.F) (Fbar := D.Fbar) (E := D.E) := by
    have hcurve : Affine.baseChange D.E D.Fbar =
        (D.E.map (algebraMap D.F D.Fbar)).toAffine := rfl
    cases hcurve
    change ∀ P ∈ iutTorsion
      ((D.E.map (algebraMap D.F D.Fbar)).toAffine.Point) 6,
      P ∈ (iutWeierstrassPointMap (E := D.E) (algebraMap D.F D.Fbar)).range
    exact D.global.six_torsion_rational
  have hfield := IutAdmissiblePrimeTorsionData.torsionField_eq_admissiblePrime
    D.prime D.isAlgClosure
  have T : IutGlobalTorsionBasis
      (D.E.map (algebraMap D.F ↥D.prime.torsionField)).toAffine.Point D.prime.ℓ := by
    rw [← hfield]
    exact P.toGlobalTorsionBasis
  exact IutTorsionQRootSource.ofTateFamily B T D.VBad D.tate
    (fun w => iutInitialThetaTateFamily_badPlace D B hPlaces w)
    hsix P.ell_pos P.ell_odd hq

end

end JoshiTeich.Act1Scene1
