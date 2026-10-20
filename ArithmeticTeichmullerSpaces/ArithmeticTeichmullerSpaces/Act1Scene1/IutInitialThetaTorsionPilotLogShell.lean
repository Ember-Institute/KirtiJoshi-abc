import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionDeRhamEvaluation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogShellBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-PILOT-LOG-SHELL
source: Joshi III `eq:bloch-kato-log-class` (3226) and the local
paper-normalized ordinary-log to log-shell calculation, applied to the actual
torsion q-root evaluation proved in the same de Rham pilot construction by
Joshi II `thm:theta-pilot-object-appears` (940--1013).
fidelity: on the original torsion completion, proves that every actual
q-root `j^2` pilot value has paper-normalized ordinary logarithm in the local
log-shell and that its normalized-log norm is the q-root norm. The existing
de Rham evaluation theorem identifies this q-root value with the same local
pilot evaluation norm. This is a local ordinary-log carrier result only; it
does not identify the logarithm with Bloch--Kato or the class with H^1_e.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTorsionPilotLogShell

open JoshiTeich.Prologue
open InitialThetaTorsionDeRhamEvaluation
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

local instance residuePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩
local instance localCharZero : CharZero (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem qrootAt_pilot_normalizedLog_mem_logShell (j : ℕ) :
    LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
      (IutInitialThetaQRootFamily.qrootAt D s.1 ^ (j ^ 2)) ∈
        LocalPadicLog.logShell (Arithmetic.residueChar s.1) := by
  have hnorm : ‖IutInitialThetaQRootFamily.qrootAt D s.1 ^ (j ^ 2)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset
      D s.1 s.2).le
  exact LocalPadicLog.paperNormalizedLog_mem_logShell
    (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    hnorm

theorem qrootAt_pilot_normalizedLog_norm (j : ℕ) :
    ‖LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
      (IutInitialThetaQRootFamily.qrootAt D s.1 ^ (j ^ 2))‖ =
      ‖IutInitialThetaQRootFamily.qrootAt D s.1‖ ^ (j ^ 2) := by
  have hnorm : ‖IutInitialThetaQRootFamily.qrootAt D s.1 ^ (j ^ 2)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset
      D s.1 s.2).le
  rw [LocalPadicLog.norm_paperNormalizedLog
    (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    hnorm, norm_pow]

theorem qrootAt_pilot_norm_eq_deRham_evaluation_norm
    (w : (iutInitialThetaTateParameterData D).places)
    (v : NumberField.FinitePlace ↥D.prime.torsionField)
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)
    (j : ℕ) :
    ‖IutInitialThetaQRootFamily.qrootAt D v ^ (j ^ 2)‖ =
      ‖InitialThetaTorsionDeRhamEvaluation.evaluation D w v hvw
        (InitialThetaTorsionDeRhamEvaluation.pilot D w v hvw j)‖ := by
  symm
  rw [InitialThetaTorsionDeRhamEvaluation.evaluation_pilot_norm, norm_pow]

end
end JoshiTeich.Act1Scene1.InitialThetaTorsionPilotLogShell
