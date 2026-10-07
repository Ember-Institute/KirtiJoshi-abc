import ArithmeticTeichmullerSpaces.Act1Scene1.IutTorsionRationality
import Iut.Cor312.ThetaData.TateFamily

/-!
source-id: IUT-COR312-TATE-FAMILY-QROOT-ADAPTER
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/TateStructure.lean` and
`refer/iut/Iut/Cor312/ThetaData/TateFamily.lean`.
fidelity: the actual IUT Tate parameter and uniformization is projected into the
group-theoretic quotient interface used by the q-root assembler. The bad-place
certificate, torsion basis, six-torsion condition, and comparison with the base
completion parameter remain explicit.
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

end

end JoshiTeich.Act1Scene1
