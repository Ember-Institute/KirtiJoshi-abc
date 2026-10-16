import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerCoordinates
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAmbientKummerLog

/-!
source-id: JT-SCENE1-INITIAL-THETA-KUMMER-COORDINATES
source: actual completion q-order, normalized class and original H1 coordinates;
Joshi III 3190--3236 as local Kummer/log comparison background.
fidelity: computes both actual classes in the continuous coordinate equivalence.
The q-root valuation coordinate is qOrder/ramIdx, while the normalized class
has zero valuation coordinate and the existing ordinary-log witness. No BK identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance coordinatePrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance coordinateCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance coordinateAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance coordinateContinuousSMul
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

theorem valuationCoordinate_qrootRationalKummerClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalCompletion.KummerValuation.valuationCoordinate s.1 (Arithmetic.residueChar s.1) rfl
      (qrootRationalKummerClass D s) =
      (Arithmetic.completionQOrder s.1
        ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s) : ℚ_[Arithmetic.residueChar s.1]) /
        Arithmetic.ramIdx s.1 := by
  change LocalCompletion.KummerValuation.valuationCoordinate s.1 (Arithmetic.residueChar s.1) rfl
    (LocalCompletion.KummerValuation.kummer s.1 (Arithmetic.residueChar s.1)
      (Ω := closure D s) (qrootFieldUnit D s)) = _
  rw [LocalCompletion.KummerValuation.valuationCoordinate_kummer,
    qroot_valuationIndex, Int.cast_neg, Int.cast_natCast, neg_div, neg_neg]

theorem kummerCoordinates_normalizedRationalClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalCompletion.KummerValuation.kummerCoordinatesContinuousEquiv s.1
      (Arithmetic.residueChar s.1) rfl (normalizedRationalClass D s) =
        (PaperLogWitnessHull.value D s, 0) := by
  apply Prod.ext
  · exact ambientLog_normalizedRationalClass D s
  · exact LocalCompletion.KummerValuation.valuationCoordinate_unit s.1
      (Arithmetic.residueChar s.1) rfl
      ⟨normalizedRationalClass D s, normalizedRationalClass_mem_unitsSubspace D s⟩

theorem rationalH1_finrank_eq_localDeg_add_one
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Module.finrank ℚ_[Arithmetic.residueChar s.1]
      (continuousCohomology 1 (LocalKummer.Rational.topRep
        (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1))) =
      Arithmetic.localDeg s.1 + 1 := by
  rw [LocalCompletion.KummerValuation.rationalH1_finrank s.1
    (Arithmetic.residueChar s.1) rfl, LocalCompletion.finrank_padic_eq_localDeg s.1 rfl]

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
