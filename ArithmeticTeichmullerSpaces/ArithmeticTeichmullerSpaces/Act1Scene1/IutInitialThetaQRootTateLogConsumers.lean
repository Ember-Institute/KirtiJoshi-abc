import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootTateLog
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAmbientKummerLog

/-!
source-id: JT-SCENE1-INITIAL-THETA-QROOT-TATE-LOG-CONSUMERS
source: actual q-root and normalized rational Kummer classes; Joshi III
3190--3236.
fidelity: evaluates the q-root-direction branch on the normalized class and
records its exact kernel.  The branch remains an ambient H1 construction.
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

local instance consumerPrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

local instance consumerCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

local instance consumerAlgebra
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl

local instance consumerContinuousSMul
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

theorem qrootTateLog_normalizedRationalClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootTateLog D s (normalizedRationalClass D s) = PaperLogWitnessHull.value D s := by
  refine Eq.mpr
    (id (congrArg (fun y => y = PaperLogWitnessHull.value D s)
      (qrootTateLog_eq_ambientLog_sub D s (normalizedRationalClass D s)))) ?_
  have hval : LocalCompletion.KummerValuation.valuationCoordinate s.1
      (Arithmetic.residueChar s.1) rfl (normalizedRationalClass D s) = 0 :=
    LocalCompletion.KummerValuation.valuationCoordinate_unit s.1
      (Arithmetic.residueChar s.1) rfl
      ⟨normalizedRationalClass D s, normalizedRationalClass_mem_unitsSubspace D s⟩
  rw [hval]
  simp only [zero_div, zero_smul, sub_zero]
  exact ambientLog_normalizedRationalClass D s

set_option maxHeartbeats 1000000 in
theorem qrootTateLog_eq_zero_iff
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (x : continuousCohomology 1 (LocalKummer.Rational.topRep
      (K := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1))) :
    qrootTateLog D s x = 0 ↔ x ∈
      ℚ_[Arithmetic.residueChar s.1] ∙ qrootClass D s := by
  apply LocalCompletion.KummerValuation.tateLog_eq_zero_iff s.1
    (Arithmetic.residueChar s.1) rfl (qrootClass D s)
      (qrootRationalKummerClass_not_mem_unitsSubspace D s) x

/-! The normalized principal-unit class is separated from the actual q-root
direction by the same Tate-log kernel. -/
set_option maxHeartbeats 1000000 in
theorem normalizedRationalClass_not_mem_qroot_span
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    normalizedRationalClass D s ∉
      ℚ_[Arithmetic.residueChar s.1] ∙ qrootClass D s := by
  intro h
  have hz : qrootTateLog D s (normalizedRationalClass D s) = 0 :=
    (qrootTateLog_eq_zero_iff D s (normalizedRationalClass D s)).2 h
  rw [qrootTateLog_normalizedRationalClass D s] at hz
  exact PaperLogWitnessHull.value_ne_zero D s hz

theorem qrootTateLog_normalizedRationalClass_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootTateLog D s (normalizedRationalClass D s) ≠ 0 := by
  rw [qrootTateLog_normalizedRationalClass D s]
  exact PaperLogWitnessHull.value_ne_zero D s

set_option maxHeartbeats 1000000 in
theorem qrootTateLog_continuous
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Continuous (qrootTateLog D s) := by
  exact LocalCompletion.KummerValuation.tateLog_continuous s.1
    (Arithmetic.residueChar s.1) rfl (qrootClass D s)
      (qrootRationalKummerClass_not_mem_unitsSubspace D s)

theorem qrootTateLog_as_generic
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    qrootTateLog D s =
      LocalCompletion.KummerValuation.tateLog s.1
        (Arithmetic.residueChar s.1) rfl (qrootClass D s)
          (qrootRationalKummerClass_not_mem_unitsSubspace D s) := rfl

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
