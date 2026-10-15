import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaKummerImageLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRationalKummerNonzero

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZED-SATURATED-KUMMER-LOG
source: actual p*-normalized rational class and ordinary witness, Joshi III 3226.
fidelity: proves the existing normalizedRationalClass belongs to the p-power
saturation of the actual principal-unit Kummer image, and evaluates the extended
logarithm as the actual paper-normalized ordinary log witness. No H^1_e/BK
identity or membership in the unsaturated principal-unit image is claimed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
noncomputable section

theorem LocalPadicLog.paperScale_eq_prime_pow (p : ℕ) :
    LocalPadicLog.paperScale p = p ^ (if p = 2 then 2 else 1) := by
  by_cases h : p = 2
  · subst p
    norm_num [LocalPadicLog.paperScale]
  · simp [LocalPadicLog.paperScale, h]

namespace PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance saturatedLogPrime (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩
local instance saturatedLogCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem normalizedRationalClass_mem_saturatedImage
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    normalizedRationalClass D s ∈ LocalPadicLog.saturatedKummerImage
      (k := localField D s) (Ω := closure D s) (Arithmetic.residueChar s.1) := by
  refine ⟨if Arithmetic.residueChar s.1 = 2 then 2 else 1, ?_⟩
  rw [← LocalPadicLog.paperScale_eq_prime_pow]
  rw [← Nat.cast_smul_eq_nsmul ℚ_[Arithmetic.residueChar s.1], scale_normalizedRationalClass]
  exact (rationalImageClass D s).2

def normalizedSaturatedClass
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedKummerImage (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) :=
  ⟨normalizedRationalClass D s, normalizedRationalClass_mem_saturatedImage D s⟩

theorem normalizedSaturatedClass_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    normalizedSaturatedClass D s ≠ 0 := by
  intro h
  apply normalizedRationalClass_ne_zero D s
  simpa [normalizedSaturatedClass] using congrArg Subtype.val h

set_option maxHeartbeats 1000000 in
theorem normalizedRationalClass_saturatedLogGraph
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedLogGraph (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
      (normalizedRationalClass D s)
      (PaperLogWitnessHull.value D s) := by
  let n : ℕ := if Arithmetic.residueChar s.1 = 2 then 2 else 1
  let a : LocalPadicLog.principalKummerImage (k := localField D s) (Ω := closure D s)
      (Arithmetic.residueChar s.1) := rationalImageClass D s
  have hxa : (Arithmetic.residueChar s.1 ^ n) • normalizedRationalClass D s = (a : _) := by
    change (Arithmetic.residueChar s.1 ^ n) • normalizedRationalClass D s =
      (rationalImageClass D s : _)
    dsimp [n]
    rw [← LocalPadicLog.paperScale_eq_prime_pow]
    rw [← Nat.cast_smul_eq_nsmul ℚ_[Arithmetic.residueChar s.1],
      scale_normalizedRationalClass]
    exact rfl
  have hya : (Arithmetic.residueChar s.1 ^ n) • PaperLogWitnessHull.value D s =
      LocalPadicLog.principalImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1) a := by
    dsimp [a, n]
    simp only [nsmul_eq_mul, Nat.cast_pow]
    rw [principalImageLog_rationalImageClass]
    rw [LocalPadicLog.paperScale_eq_prime_pow]
    rw [Nat.cast_pow]
  exact ⟨n, a, hxa, hya⟩

theorem normalizedSaturatedClass_saturatedImageLog_eq_value
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (normalizedSaturatedClass D s) = PaperLogWitnessHull.value D s := by
  apply LocalPadicLog.saturatedImageLog_eq_of_graph
  exact normalizedRationalClass_saturatedLogGraph D s

theorem normalizedSaturatedClass_saturatedImageLog_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
        (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
        (normalizedSaturatedClass D s) ≠ 0 := by
  rw [normalizedSaturatedClass_saturatedImageLog_eq_value D s]
  exact PaperLogWitnessHull.value_ne_zero D s

set_option maxHeartbeats 1000000 in
theorem normalizedSaturatedClass_nsmul_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    {r : ℕ} (hr : r ≠ 0) :
    r • normalizedSaturatedClass D s ≠ 0 := by
  intro h
  have hlog := congrArg
    (LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1)) h
  rw [map_nsmul, map_zero] at hlog
  rw [normalizedSaturatedClass_saturatedImageLog_eq_value D s] at hlog
  have hr' : (r : localField D s) ≠ 0 :=
    Nat.cast_ne_zero.mpr hr
  have hmul : (r : localField D s) * PaperLogWitnessHull.value D s = 0 := by
    simpa only [nsmul_eq_mul] using hlog
  exact (PaperLogWitnessHull.value_ne_zero D s)
    ((mul_eq_zero.mp hmul).resolve_left hr')

set_option maxHeartbeats 1000000 in
theorem normalizedSaturatedClass_zsmul_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    {r : ℤ} (hr : r ≠ 0) :
    r • normalizedSaturatedClass D s ≠ 0 := by
  intro h
  have hlog := congrArg
    (LocalPadicLog.saturatedImageLog (Arithmetic.residueChar s.1)
      (InitialThetaLogWitness.norm_residueChar_lt_one s.1)) h
  rw [map_zsmul, map_zero] at hlog
  rw [normalizedSaturatedClass_saturatedImageLog_eq_value D s] at hlog
  have hr' : (r : localField D s) ≠ 0 :=
    Int.cast_ne_zero.mpr hr
  have hmul : (r : localField D s) * PaperLogWitnessHull.value D s = 0 := by
    simpa only [zsmul_eq_mul] using hlog
  exact (PaperLogWitnessHull.value_ne_zero D s)
    ((mul_eq_zero.mp hmul).resolve_left hr')

end PrincipalUnitKummer
end
end JoshiTeich.Act1Scene1
