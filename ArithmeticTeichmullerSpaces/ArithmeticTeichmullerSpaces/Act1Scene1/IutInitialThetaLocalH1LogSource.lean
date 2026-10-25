import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRationalKummer
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLogCalibration
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedIntegralLog

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-INITIAL-THETA-LOCAL-H1-LOG-SOURCE
source: the actual principal-unit Kummer class, rational H¹ representative,
integral image class, and the ordinary/normalized log calibration in
`IutInitialThetaRationalKummer.lean`, `IutInitialThetaLogCalibration.lean`,
and `IutInitialThetaNormalizedIntegralLog.lean`.
fidelity: packages the same local actual source and both proved logarithmic
normalizations. It does not call the standard H¹ carrier H¹ₑ, does not create
a crystalline carrier, and does not assert a Bloch--Kato comparison.
boundary: Scene1/Derived; local actual cohomology/log source only.
-/

namespace InitialThetaLocalH1LogSource

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

local instance sourcePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩
local instance sourceCharZero : CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance sourceAlgebra : Algebra ℚ_[Arithmetic.residueChar s.1]
    (PrincipalUnitKummer.localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance sourceContinuousSMul : ContinuousSMul ℚ_[Arithmetic.residueChar s.1]
    (PrincipalUnitKummer.localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

abbrev AmbientH1 :=
  continuousCohomology 1
    (LocalKummer.Rational.topRep (K := PrincipalUnitKummer.localField D s)
      (Ω := PrincipalUnitKummer.closure D s) (Arithmetic.residueChar s.1))

abbrev IntegralClass :=
  LocalPadicLog.integralKummerSubmodule (Ω := PrincipalUnitKummer.closure D s)
    (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)

set_option maxHeartbeats 1000000 in
structure Data : Type (u + 1) where
  ambientClass : AmbientH1 D s
  integralClass : IntegralClass D s
  ordinaryLog : PrincipalUnitKummer.localField D s
  normalizedLog : PrincipalUnitKummer.localField D s
  ambientClass_eq : ambientClass = PrincipalUnitKummer.rationalClass D s
  ordinaryLog_eq : ordinaryLog =
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) :
      PrincipalUnitKummer.localField D s) * PaperLogWitnessHull.value D s
  normalizedLog_eq : normalizedLog = PaperLogWitnessHull.value D s

noncomputable def canonical : Data D s where
  ambientClass := PrincipalUnitKummer.rationalClass D s
  integralClass := PrincipalUnitKummer.actualIntegralImageClass D s
  ordinaryLog := LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (PrincipalUnitKummer.actualIntegralImageClass D s).1
  normalizedLog := LocalPadicLog.normalizedRationalLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (PrincipalUnitKummer.actualIntegralImageClass D s).1
  ambientClass_eq := rfl
  ordinaryLog_eq := PrincipalUnitKummer.originalIntegralImageClass_ordinaryLog D s
  normalizedLog_eq := PrincipalUnitKummer.originalIntegralImageClass_normalizedRationalLog D s

theorem canonical_ambientClass_eq :
    (canonical D s).ambientClass = PrincipalUnitKummer.rationalClass D s := rfl

theorem canonical_normalizedLog_eq :
    (canonical D s).normalizedLog = PaperLogWitnessHull.value D s :=
  (canonical D s).normalizedLog_eq

end InitialThetaLocalH1LogSource

end
end JoshiTeich.Act1Scene1
