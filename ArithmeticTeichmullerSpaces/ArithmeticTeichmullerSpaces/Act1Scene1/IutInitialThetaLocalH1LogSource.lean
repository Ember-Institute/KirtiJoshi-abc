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

/-- Keep the integral-source conversions behind typed functions. -/
def actualIntegral : IntegralClass D s := PrincipalUnitKummer.actualIntegralImageClass D s

def integralToAmbient (x : IntegralClass D s) : AmbientH1 D s := x.1.1

def ordinaryLogOfIntegral (x : IntegralClass D s) : PrincipalUnitKummer.localField D s :=
  LocalPadicLog.saturatedPadicLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) x.1

def normalizedLogOfIntegral (x : IntegralClass D s) : PrincipalUnitKummer.localField D s :=
  LocalPadicLog.normalizedRationalLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) x.1

theorem integralToAmbient_actual :
    integralToAmbient D s (actualIntegral D s) = PrincipalUnitKummer.rationalClass D s :=
  (PrincipalUnitKummer.actualIntegralImageClass_coefficient D s).trans
    (PrincipalUnitKummer.rationalClass_eq_changeCoefficients D s).symm

theorem ordinaryLogOfIntegral_actual :
    ordinaryLogOfIntegral D s (actualIntegral D s) =
      (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) :
        PrincipalUnitKummer.localField D s) * PaperLogWitnessHull.value D s :=
  PrincipalUnitKummer.originalIntegralImageClass_ordinaryLog D s

theorem normalizedLogOfIntegral_actual :
    normalizedLogOfIntegral D s (actualIntegral D s) = PaperLogWitnessHull.value D s :=
  PrincipalUnitKummer.originalIntegralImageClass_normalizedRationalLog D s

set_option maxHeartbeats 1000000 in
structure Data : Type (u + 1) where
  ambientClass : AmbientH1 D s
  integralClass : IntegralClass D s
  ordinaryLog : PrincipalUnitKummer.localField D s
  normalizedLog : PrincipalUnitKummer.localField D s
  integralClass_eq : integralClass = actualIntegral D s
  ambientClass_from_integral : integralToAmbient D s integralClass = ambientClass
  ordinaryLog_from_integral : ordinaryLog = ordinaryLogOfIntegral D s integralClass
  normalizedLog_from_integral : normalizedLog = normalizedLogOfIntegral D s integralClass
  ambientClass_eq : ambientClass = PrincipalUnitKummer.rationalClass D s
  ordinaryLog_eq : ordinaryLog =
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) :
      PrincipalUnitKummer.localField D s) * PaperLogWitnessHull.value D s
  normalizedLog_eq : normalizedLog = PaperLogWitnessHull.value D s

noncomputable def canonical : Data D s where
  ambientClass := PrincipalUnitKummer.rationalClass D s
  integralClass := actualIntegral D s
  ordinaryLog := ordinaryLogOfIntegral D s (actualIntegral D s)
  normalizedLog := normalizedLogOfIntegral D s (actualIntegral D s)
  integralClass_eq := rfl
  ambientClass_from_integral := integralToAmbient_actual D s
  ordinaryLog_from_integral := rfl
  normalizedLog_from_integral := rfl
  ambientClass_eq := rfl
  ordinaryLog_eq := ordinaryLogOfIntegral_actual D s
  normalizedLog_eq := normalizedLogOfIntegral_actual D s

theorem canonical_ambientClass_eq :
    (canonical D s).ambientClass = PrincipalUnitKummer.rationalClass D s := rfl

/-- The stored ambient class is the coefficient image of an integral class. -/
theorem Data.ambientClass_has_integralLift (X : Data D s) :
    ∃ x, LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1) x =
      X.ambientClass := by
  obtain ⟨x, hx⟩ := (LocalPadicLog.mem_integralKummerSubmodule_iff
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    X.integralClass.1).mp X.integralClass.2
  exact ⟨x, hx.trans X.ambientClass_from_integral⟩

/-- Recover the value from the stored integral source and its logarithm. -/
theorem Data.normalizedLog_eq_of_integral (X : Data D s) :
    X.normalizedLog = PaperLogWitnessHull.value D s := by
  rw [X.normalizedLog_from_integral, X.integralClass_eq]
  exact normalizedLogOfIntegral_actual D s

theorem canonical_normalizedLog_eq :
    (canonical D s).normalizedLog = PaperLogWitnessHull.value D s :=
  Data.normalizedLog_eq_of_integral D s (canonical D s)

end InitialThetaLocalH1LogSource

end
end JoshiTeich.Act1Scene1
