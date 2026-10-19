import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogClosureTransport
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSaturatedKummerLog

/-!
source-id: JT-SCENE1-INITIAL-THETA-CLOSURE-LOG
source: Joshi I preferred-closure Kummer theory (1588--1632), III
principal-unit and normalized logarithmic witnesses (3190--3236).
fidelity: for the original D/local completion, produces an algebraic closure
comparison to any algebraically closed integral extension. The original
principal-unit class and divided saturated class transport into that closure;
their ordinary logarithms retain the exact original p*-witness formulas.
No closure equivalence, group marking or log compatibility is supplied.
Fixed completion only; no H1_e/BK or full holomorphoid collation identity.
Original proofs; Prologue-R5 unchanged.
-/
namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
local instance residuePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩
local instance baseCharZero : CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
variable (Ξ : Type u) [Field Ξ] [Algebra (localField D s) Ξ]
variable [Algebra.IsIntegral (localField D s) Ξ] [IsAlgClosed Ξ]
private theorem targetCharZero (E Ξ : Type u) [Field E] [CharZero E]
    [Field Ξ] [Algebra E Ξ] : CharZero Ξ :=
  charZero_of_injective_ringHom (algebraMap E Ξ).injective
local instance targetIsAlgClosure : IsAlgClosure (localField D s) Ξ :=
  ⟨inferInstance, inferInstance⟩

def preferredEquiv : closure D s ≃ₐ[localField D s] Ξ :=
  IsAlgClosure.equiv (localField D s) (closure D s) Ξ

def imageClass : letI := targetCharZero (localField D s) Ξ
    LocalPadicLog.principalKummerImage
      (k := localField D s) (Ω := Ξ) (Arithmetic.residueChar s.1) := by
  letI := targetCharZero (localField D s) Ξ
  exact LocalPadicLog.ClosureTransport.principalImageEquiv (preferredEquiv D s Ξ)
    (Arithmetic.residueChar s.1) (rationalImageClass D s)

theorem imageClass_eq_kummer :
    let := targetCharZero (localField D s) Ξ
    (imageClass D s Ξ).1 =
      (LocalKummer.Rational.kummerHom (K := localField D s) (Ω := Ξ)
        (Arithmetic.residueChar s.1) (actualPrincipalUnit D s).1).toAdd := by
  let := targetCharZero (localField D s) Ξ
  exact LocalPadicLog.ClosureTransport.kummerHom (preferredEquiv D s Ξ)
    (Arithmetic.residueChar s.1) (actualPrincipalUnit D s).1

theorem imageClass_log :
    let := targetCharZero (localField D s) Ξ
    LocalPadicLog.principalImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (imageClass D s Ξ) =
        (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s) *
          PaperLogWitnessHull.value D s := by
  let := targetCharZero (localField D s) Ξ
  rw [imageClass, LocalPadicLog.ClosureTransport.principalImageLog_eq]
  exact principalImageLog_rationalImageClass D s

theorem imageClass_normalizedLog :
    let := targetCharZero (localField D s) Ξ
    (LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : localField D s)⁻¹ *
      LocalPadicLog.principalImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (imageClass D s Ξ) =
      PaperLogWitnessHull.value D s := by
  let := targetCharZero (localField D s) Ξ
  rw [imageClass_log, inv_mul_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1))

def dividedClass : letI := targetCharZero (localField D s) Ξ
    LocalPadicLog.saturatedKummerImage
      (k := localField D s) (Ω := Ξ) (Arithmetic.residueChar s.1) := by
  letI := targetCharZero (localField D s) Ξ
  exact LocalPadicLog.ClosureTransport.saturatedEquiv (preferredEquiv D s Ξ)
    (Arithmetic.residueChar s.1) (normalizedSaturatedClass D s)

theorem dividedClass_log :
    let := targetCharZero (localField D s) Ξ
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (dividedClass D s Ξ) =
        PaperLogWitnessHull.value D s := by
  let := targetCharZero (localField D s) Ξ
  rw [dividedClass, LocalPadicLog.ClosureTransport.saturatedImageLog_eq]
  exact normalizedSaturatedClass_saturatedImageLog_eq_value D s

theorem dividedClass_ne_zero : dividedClass D s Ξ ≠ 0 := by
  let := targetCharZero (localField D s) Ξ
  intro h
  have he := congrArg (LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)) h
  rw [dividedClass_log, map_zero] at he
  exact PaperLogWitnessHull.value_ne_zero D s he

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog
