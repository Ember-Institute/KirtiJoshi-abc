import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionPilotLogShell

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped Valued

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-PILOT-LOG-SHELL-SOURCE
source: the actual q-root pilot log-shell and norm identities from
`IutInitialThetaTorsionPilotLogShell.lean` and the de Rham evaluation.
fidelity: packages the local normalized-log shell source without identifying
it with a Bloch--Kato logarithm or H¹ₑ class.
boundary: Scene1/Derived; local torsion q-root/log carrier only.
-/

namespace InitialThetaCanonicalTorsionPilotLogShellSource

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

local instance sourcePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩
local instance sourceCharZero : CharZero (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

abbrev LocalField := s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField

def qrootAt : LocalField D s := IutInitialThetaQRootFamily.qrootAt D s.1

def normalizedLog (j : ℕ) : LocalField D s :=
  LocalPadicLog.paperNormalizedLog (Arithmetic.residueChar s.1)
    (qrootAt D s ^ (j ^ 2))

structure Data : Type (u + 1) where
  logShell_mem : ∀ j, normalizedLog D s j ∈
    LocalPadicLog.logShell (Arithmetic.residueChar s.1)
  norm_eq_qroot : ∀ j, ‖normalizedLog D s j‖ = ‖qrootAt D s‖ ^ (j ^ 2)

noncomputable def canonical : Data D s where
  logShell_mem j :=
    InitialThetaTorsionPilotLogShell.qrootAt_pilot_normalizedLog_mem_logShell D s j
  norm_eq_qroot j :=
    InitialThetaTorsionPilotLogShell.qrootAt_pilot_normalizedLog_norm D s j

theorem canonical_norm_eq_qroot (j : ℕ) :
    ‖normalizedLog D s j‖ = ‖qrootAt D s‖ ^ (j ^ 2) :=
  (canonical D s).norm_eq_qroot j

theorem canonical_normalizedLog_ne_zero (j : ℕ) :
    normalizedLog D s j ≠ 0 := by
  intro h
  have hnorm : ‖qrootAt D s‖ ^ (j ^ 2) = 0 := by
    rw [← canonical_norm_eq_qroot D s j, h, norm_zero]
  have hqnorm : ‖qrootAt D s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (IutInitialThetaQRootFamily.qrootAt_ne_zero D s.1)
  exact (pow_ne_zero _ hqnorm) hnorm

theorem canonical_normalizedLog_norm_lt_one (j : ℕ) (hj : 0 < j) :
    ‖normalizedLog D s j‖ < 1 := by
  rw [canonical_norm_eq_qroot D s j]
  have hj2 : j ^ 2 ≠ 0 := by positivity
  exact pow_lt_one₀ (norm_nonneg _) (
    IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset D s.1 s.2)
    hj2

theorem canonical_normalizedLog_norm_zero :
    ‖normalizedLog D s 0‖ = 1 := by
  rw [canonical_norm_eq_qroot D s 0]
  simp

theorem canonical_normalizedLog_mem_logShell (j : ℕ) :
    normalizedLog D s j ∈ LocalPadicLog.logShell (Arithmetic.residueChar s.1) :=
  (canonical D s).logShell_mem j

theorem canonical_normalizedLog_norm_pos (j : ℕ) :
    0 < ‖normalizedLog D s j‖ :=
  norm_pos_iff.mpr (canonical_normalizedLog_ne_zero D s j)

end InitialThetaCanonicalTorsionPilotLogShellSource

end
end JoshiTeich.Act1Scene1
