import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionGaloisFiberMass
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaGaloisQRootChoice

/-!
source-id: JT-SCENE1-INITIAL-THETA-GALOIS-FIBER-MASS
source: Joshi III `eq:weights`, actual full torsion over-place support, the
Galois representation-kernel field, and q-root norm choice independence.
fidelity: constructs the complete fibre over an actual base source place,
computes its multiplicity and q-pilot mass, and pushes the corrected q-root
log sum to one representative with the computed mass. No mass-one law is used.
boundary: Scene1/Derived; this F-place carrier is not identified with paper L'.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue NumberField
open scoped BigOperators
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance fiberTorsionGalois : IsGalois D.F ↥D.prime.torsionField :=
  IsGalois.of_fixedField_normal_subgroup D.prime.rep.ker

def iutInitialThetaTorsionBaseFiber
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    Finset (FinitePlace ↥D.prime.torsionField) :=
  (finite_places_liesOver (K := ↥D.prime.torsionField) b.1).toFinset

theorem mem_iutInitialThetaTorsionBaseFiber_iff
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset)
    (v : FinitePlace ↥D.prime.torsionField) :
    v ∈ iutInitialThetaTorsionBaseFiber D b ↔
      Ideal.LiesOver v.maximalIdeal.asIdeal b.1.maximalIdeal.asIdeal := by
  rw [iutInitialThetaTorsionBaseFiber, Set.Finite.mem_toFinset]
  rfl

theorem iutInitialThetaTorsionBaseFiber_card_mul_relativeDegree
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (iutInitialThetaTorsionBaseFiber D
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s)).card *
      (Arithmetic.relRamIdx s.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 *
        Arithmetic.relInertDeg s.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1) =
      Module.finrank D.F ↥D.prime.torsionField := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  exact LocalCompletion.card_mul_relativeDegree_eq_finrank (R.basePlace s).1
    (iutInitialThetaTorsionBaseFiber D (R.basePlace s))
    (mem_iutInitialThetaTorsionBaseFiber_iff D (R.basePlace s)) s.1
    ((mem_iutInitialThetaTorsionBaseFiber_iff D (R.basePlace s) s.1).mpr (R.liesOver s))

theorem iutInitialThetaTorsionBaseFiber_mass_eq_base_div_relativeRamIdx
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (∑ v ∈ iutInitialThetaTorsionBaseFiber D
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s),
      Arithmetic.qPilotWeight v) =
      Arithmetic.qPilotWeight ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 /
        (Arithmetic.relRamIdx s.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 : ℝ) := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  exact LocalCompletion.qPilotWeight_sum_eq_base_div_relativeRamIdx (R.basePlace s).1
    (iutInitialThetaTorsionBaseFiber D (R.basePlace s))
    (mem_iutInitialThetaTorsionBaseFiber_iff D (R.basePlace s)) s.1
    ((mem_iutInitialThetaTorsionBaseFiber_iff D (R.basePlace s) s.1).mpr (R.liesOver s))

/-- Every place in the complete fibre belongs to the same actual q-root source. -/
def iutInitialThetaTorsionBaseFiberSource
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset)
    (v : iutInitialThetaTorsionBaseFiber D b) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  refine ⟨v.1, ?_⟩
  change v.1 ∈ iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
    B.badPlaces B.badPlaces_finite
  apply (mem_iutBadPlacesOverFinset_iff B.badPlaces B.badPlaces_finite v.1).mpr
  exact ⟨b.1, B.mem_badPlaces b, (mem_iutInitialThetaTorsionBaseFiber_iff D b v.1).mp v.2⟩

theorem iutInitialThetaTorsionBaseFiberSource_basePlace
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset)
    (v : iutInitialThetaTorsionBaseFiber D b) :
    (iutInitialThetaOddSupportTorsionQRootSource D).basePlace
      (iutInitialThetaTorsionBaseFiberSource D b v) = b := by
  apply Subtype.ext
  have hsource := (iutInitialThetaOddSupportTorsionQRootSource D).liesOver
    (iutInitialThetaTorsionBaseFiberSource D b v)
  have hbase := (mem_iutInitialThetaTorsionBaseFiber_iff D b v.1).mp v.2
  exact (iutPlaceUnder_eq_of_liesOver hsource).trans (iutPlaceUnder_eq_of_liesOver hbase).symm

/-- Full-fibre regrouping retains its computed mass instead of replacing it by one. -/
theorem iutInitialThetaTorsionBaseFiber_weightedPaperLogSum
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (∑ v : iutInitialThetaTorsionBaseFiber D
        ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s),
      Arithmetic.qPilotWeight v.1 *
        (-Real.log (actualPaperRootNorm D
          (iutInitialThetaTorsionBaseFiberSource D
            ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s) v)))) =
      (Arithmetic.qPilotWeight ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 /
        (Arithmetic.relRamIdx s.1
          ((iutInitialThetaOddSupportTorsionQRootSource D).basePlace s).1 : ℝ)) *
        (-Real.log (actualPaperRootNorm D s)) := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  have hterm (v : iutInitialThetaTorsionBaseFiber D (R.basePlace s)) :
      actualPaperRootNorm D (iutInitialThetaTorsionBaseFiberSource D (R.basePlace s) v) =
        actualPaperRootNorm D s :=
    actualPaperRootNorm_eq_of_same_basePlace D _ s
      (iutInitialThetaTorsionBaseFiberSource_basePlace D (R.basePlace s) v)
  calc
    _ = (∑ v : iutInitialThetaTorsionBaseFiber D (R.basePlace s), Arithmetic.qPilotWeight v.1) *
        (-Real.log (actualPaperRootNorm D s)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun v _ => by rw [hterm v]
    _ = _ := by
      rw [Finset.sum_coe_sort
        (s := iutInitialThetaTorsionBaseFiber D (R.basePlace s))
        (f := Arithmetic.qPilotWeight),
        iutInitialThetaTorsionBaseFiber_mass_eq_base_div_relativeRamIdx D s]

end
end JoshiTeich.Act1Scene1
