import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionPilotIntegralClasses
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizedLogHull

/-!
source-id: JT-SCENE1-TORSION-PILOT-INTEGRAL-TENSOR
source: Joshi III `eq:bloch-kato-log-class` and standard-point tensor hull;
the actual integral torsion pilot classes and equal-norm normalization hull.
fidelity: takes the normalized logs of every integral class in the finite
pilot range at one supported torsion place. Their pure tensor is a unit in
the tensor log-shell, and its normalization hull equals the principal region
of the tensor of the original q-root powers. All classes use the same actual
completion and algebraic closure. No reference implementation is copied.
boundary: Scene1/Derived; this repeated-place finite packet is not identified
with the paper procession, H¹ₑ/BK, or a cross-holomorphoid theta locus.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTorsionPilotIntegralTensor
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

local instance sourcePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

def packet : LocalCompletion.Packet ↥D.prime.torsionField
    (Arithmetic.residueChar s.1) (Fin (D.prime.ℓ + 1)) :=
  ⟨fun _ => s.1, fun _ => rfl⟩

def rootScalars (j : Fin (D.prime.ℓ + 1)) : (packet D s).Factor j :=
  InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s ^ (j.val ^ 2)

def logScalars (j : Fin (D.prime.ℓ + 1)) : (packet D s).Factor j :=
  InitialThetaTorsionPilotIntegralClasses.logValue D s
    (InitialThetaTorsionPilotIntegralClasses.finitePilot D s j)

theorem logScalars_eq_paperLogScalars :
    logScalars D s = (packet D s).paperLogScalars (rootScalars D s) := by
  funext j
  exact InitialThetaTorsionPilotIntegralClasses.finitePilot_logValue D s j

theorem rootScalars_ne_zero (j : Fin (D.prime.ℓ + 1)) : rootScalars D s j ≠ 0 :=
  pow_ne_zero _ (IutInitialThetaQRootFamily.qrootAt_ne_zero D s.1)

theorem rootScalars_norm_le_one (j : Fin (D.prime.ℓ + 1)) : ‖rootScalars D s j‖ ≤ 1 := by
  change ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s ^ (j.val ^ 2)‖ ≤ 1
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _)
    (IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset D s.1 s.2).le

def witness : (packet D s).Tensor := (packet D s).pure (logScalars D s)

theorem witness_isUnit : IsUnit (witness D s) :=
  (packet D s).pure_isUnit _
    (InitialThetaTorsionPilotIntegralClasses.finitePilot_logValue_ne_zero D s)

theorem witness_mem_tensorLogShell : witness D s ∈ (packet D s).tensorLogShell := by
  apply (packet D s).pure_mem_lattice
  intro j
  rw [logScalars, InitialThetaTorsionPilotIntegralClasses.finitePilot_logValue]
  exact InitialThetaCanonicalTorsionPilotLogShellSource.canonical_normalizedLog_mem_logShell
    D s j.val

theorem witness_singletonHull_eq_root_principalRegion :
    ((packet D s).normalizationHull {witness D s} : Set (packet D s).Tensor) =
      (packet D s).principalRegion ((packet D s).pure (rootScalars D s)) := by
  rw [witness, logScalars_eq_paperLogScalars]
  exact (packet D s).singletonHull_paperLogScalars (rootScalars D s)
    (rootScalars_ne_zero D s) (rootScalars_norm_le_one D s)

end
end JoshiTeich.Act1Scene1.InitialThetaTorsionPilotIntegralTensor
