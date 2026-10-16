import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerLogShellNormalization
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionPadicAlgebra
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSaturatedExpWitness
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogShellBridge

/-!
source-id: JT-SCENE1-ACTUAL-KUMMER-LOG-SHELL
source: actual local completions and paper-normalized witnesses, Joshi III
2843--2853 and 3226. No new reference code is copied.
fidelity: derives the Q_p structure and finite dimension from the actual
completion embedding. The existing normalized rational class belongs to
the normalized Kummer shell and its shell logarithm is the original witness.
boundary: Scene1/Derived; H1e/BK and integral-H1 intersection remain open.
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance shellPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance shellCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective
local instance shellAlgebra (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Algebra ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.padicAlgebra (w := s.1) rfl
local instance shellFinite (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    FiniteDimensional ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  LocalCompletion.finite_padicAlgebra (w := s.1) rfl
local instance shellContinuousSMul (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ContinuousSMul ℚ_[Arithmetic.residueChar s.1] (localField D s) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb (w := s.1) rfl)

def normalizedPadicClass (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedKummerPadicSubmodule (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1) :=
  ⟨normalizedRationalClass D s, normalizedRationalClass_mem_saturatedImage D s⟩

set_option maxHeartbeats 1000000 in
theorem normalizedPadicClass_mem_logShell
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    normalizedPadicClass D s ∈ LocalPadicLog.normalizedKummerShell
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1) := by
  change LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (normalizedSaturatedClass D s) ∈
      LocalPadicLog.logShell (Arithmetic.residueChar s.1)
  rw [normalizedSaturatedClass_saturatedImageLog_eq_value]
  exact PaperLogWitnessHull.value_mem_logShell D s

def normalizedShellClass (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.normalizedKummerShell (Ω := closure D s)
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1) :=
  ⟨normalizedPadicClass D s, normalizedPadicClass_mem_logShell D s⟩

theorem normalizedShellClass_log_eq_value
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalPadicLog.normalizedKummerShellLogEquiv (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1) (normalizedShellClass D s) :
        localField D s) = PaperLogWitnessHull.value D s :=
  normalizedSaturatedClass_saturatedImageLog_eq_value D s

theorem normalizedShellClass_exp_eq_class
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (LocalPadicLog.normalizedKummerShellLogEquiv (Ω := closure D s)
      (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)).symm
        ⟨PaperLogWitnessHull.value D s, PaperLogWitnessHull.value_mem_logShell D s⟩ =
      normalizedShellClass D s := by
  let e := LocalPadicLog.normalizedKummerShellLogEquiv (Ω := closure D s)
    (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
  have hlog : e (normalizedShellClass D s) =
      ⟨PaperLogWitnessHull.value D s, PaperLogWitnessHull.value_mem_logShell D s⟩ :=
    Subtype.ext (normalizedShellClass_log_eq_value D s)
  exact (congrArg e.symm hlog).symm.trans (e.symm_apply_apply _)

theorem normalizedPadicClass_has_paperPrincipalRepresentative
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ∃ a : Additive (LocalPadicLog.principalUnits (k := localField D s)),
      LocalPadicLog.paperPrincipalSaturatedClass (Ω := closure D s)
        (Arithmetic.residueChar s.1) (InitialThetaLogWitness.norm_residueChar_lt_one s.1) a =
          normalizedPadicClass D s :=
  (LocalPadicLog.mem_normalizedKummerShell_iff_paperScale _ _ _).mp
    (normalizedPadicClass_mem_logShell D s)

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
