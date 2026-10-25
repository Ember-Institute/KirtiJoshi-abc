import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionPilotIntegralTensor
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationLogVolume

/-!
source-id: JT-SCENE1-POSITIVE-PILOT-INTEGRAL-TENSOR
source: Joshi III `eq:multiplicative-coh-class` and the finite product over
j=1,...,(ell-1)/2 in `th:moccor-Mochizuki-form1`, followed by
`le:volume-lemma3`.
fidelity: selects precisely the positive half-range of actual integral
Kummer images and forms their normalized ordinary-log tensor at a single
supported completion. Computes its compact normalization hull, positive
finite Haar measure, and dimension-normalized real log-volume, retaining
the actual local degree. Original proofs; no reference code copied.
boundary: Scene1/Derived. The factors repeat one completion; they are not
different untilts. Neither BK/theta-locus identity nor the paper's
j^2/ellStar^2 rescaling or paper weighted volume is asserted.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPositivePilotIntegralTensor

open JoshiTeich.Prologue
open scoped BigOperators Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)

abbrev Index := Fin ((D.prime.ℓ - 1) / 2)

def index (j : Index D) : Fin (D.prime.ℓ + 1) :=
  ⟨j.val + 1, by have h := j.isLt; omega⟩

theorem index_injective : Function.Injective (index D) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  exact Nat.add_right_cancel hv

local instance sourcePrime : Fact (Arithmetic.residueChar s.1).Prime :=
  ⟨Arithmetic.residueChar_prime s.1⟩

def packet : LocalCompletion.Packet ↥D.prime.torsionField
    (Arithmetic.residueChar s.1) (Index D) :=
  ⟨fun _ => s.1, fun _ => rfl⟩

def classes (j : Index D) :=
  InitialThetaTorsionPilotIntegralClasses.finitePilot D s (index D j)

theorem classes_injective : Function.Injective (classes D s) :=
  (InitialThetaTorsionPilotIntegralClasses.finitePilot_injective D s).comp
    (index_injective D)

def rootScalars (j : Index D) : (packet D s).Factor j :=
  InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s ^ ((j.val + 1) ^ 2)

def logScalars (j : Index D) : (packet D s).Factor j :=
  InitialThetaTorsionPilotIntegralClasses.logValue D s (classes D s j)

theorem logScalars_eq_paperLogScalars :
    logScalars D s = (packet D s).paperLogScalars (rootScalars D s) := by
  funext j
  exact InitialThetaTorsionPilotIntegralClasses.finitePilot_logValue D s (index D j)

theorem rootScalars_ne_zero (j : Index D) : rootScalars D s j ≠ 0 :=
  pow_ne_zero _ (IutInitialThetaQRootFamily.qrootAt_ne_zero D s.1)

theorem rootScalars_norm_lt_one (j : Index D) : ‖rootScalars D s j‖ < 1 := by
  change ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s ^
    ((j.val + 1) ^ 2)‖ < 1
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _)
    (IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset D s.1 s.2)
    (by positivity)

def witness : (packet D s).Tensor := (packet D s).pure (logScalars D s)

theorem witness_isUnit : IsUnit (witness D s) :=
  (packet D s).pure_isUnit _ (fun j =>
    InitialThetaTorsionPilotIntegralClasses.finitePilot_logValue_ne_zero D s (index D j))

theorem witness_mem_tensorLogShell : witness D s ∈ (packet D s).tensorLogShell := by
  apply (packet D s).pure_mem_lattice
  intro j
  change InitialThetaTorsionPilotIntegralClasses.logValue D s
    (InitialThetaTorsionPilotIntegralClasses.finitePilot D s (index D j)) ∈ _
  rw [InitialThetaTorsionPilotIntegralClasses.finitePilot_logValue]
  exact InitialThetaCanonicalTorsionPilotLogShellSource.canonical_normalizedLog_mem_logShell
    D s (index D j).val

def region : Set (packet D s).Tensor :=
  (packet D s).normalizationHull {witness D s}

theorem region_eq_root_principalRegion :
    region D s = (packet D s).principalRegion ((packet D s).pure (rootScalars D s)) := by
  rw [region, witness, logScalars_eq_paperLogScalars]
  exact (packet D s).singletonHull_paperLogScalars _ (rootScalars_ne_zero D s)
    (fun j => (rootScalars_norm_lt_one D s j).le)

theorem region_isCompact : IsCompact (region D s) := by
  rw [region_eq_root_principalRegion]
  exact (packet D s).principalRegion_isCompact _
    ((packet D s).pure_isUnit _ (rootScalars_ne_zero D s))

theorem region_haar_pos_lt_top :
    0 < (packet D s).normalizationHaar (region D s) ∧
      (packet D s).normalizationHaar (region D s) < ⊤ := by
  rw [region_eq_root_principalRegion]
  exact (packet D s).principalRegion_haar_pos_lt_top _
    ((packet D s).pure_isUnit _ (rootScalars_ne_zero D s))

theorem region_logVolume_eq_square_sum :
    (packet D s).normalizationLogVolume (region D s) =
      (∑ j : Index D, (((j.val + 1) ^ 2 : ℕ) : ℝ)) *
        (Real.log ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s‖ /
          (Arithmetic.localDeg s.1 : ℝ)) := by
  rw [region_eq_root_principalRegion,
    (packet D s).normalizationLogVolume_pure_principalRegion _ (rootScalars_ne_zero D s),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  change Real.log ‖InitialThetaCanonicalTorsionPilotLogShellSource.qrootAt D s ^
    ((j.val + 1) ^ 2)‖ / (Arithmetic.localDeg s.1 : ℝ) = _
  rw [norm_pow, Real.log_pow]
  ring

theorem region_logVolume_neg : (packet D s).normalizationLogVolume (region D s) < 0 := by
  rw [region_logVolume_eq_square_sum]
  have hn : 0 < (D.prime.ℓ - 1) / 2 := by have h := D.prime.five_le; omega
  have hsum : 0 < ∑ j : Index D, (((j.val + 1) ^ 2 : ℕ) : ℝ) := by
    apply Finset.sum_pos'
    · intro j hj; positivity
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _, by norm_num⟩
  apply mul_neg_of_pos_of_neg hsum
  apply div_neg_of_neg_of_pos
  · exact Real.log_neg (norm_pos_iff.mpr (IutInitialThetaQRootFamily.qrootAt_ne_zero D s.1))
      (IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset D s.1 s.2)
  · exact_mod_cast Arithmetic.localDeg_pos s.1

end
end JoshiTeich.Act1Scene1.InitialThetaPositivePilotIntegralTensor
