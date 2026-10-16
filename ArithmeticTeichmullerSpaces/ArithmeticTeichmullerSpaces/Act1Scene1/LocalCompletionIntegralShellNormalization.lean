import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerIntegralLogLattice
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionUnitLogarithm

/-!
source-id: JT-SCENE1-ACTUAL-INTEGRAL-SHELL-NORMALIZATION
source: actual finite completions and the full unit logarithm, Joshi III
2843--2853 and 3226--3236. No reference code is copied.
fidelity: the actual full-unit log image is strictly smaller than the old
p*-scaled shell. Multiplying the shell by p* recovers that image. There
are shell classes without integral lifts; no such assertion is made about
the particular q-root witness, and no BK comparison is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open NumberField
open JoshiTeich.Prologue.Arithmetic
open scoped Valued
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
local instance normalizationPrime : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩
local instance normalizationCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local instance normalizationAlgebra : Algebra ℚ_[residueChar w] (completionAt K w) :=
  padicAlgebra (w := w) rfl
local instance normalizationContinuousSMul : ContinuousSMul ℚ_[residueChar w] (completionAt K w) :=
  continuousSMul_of_algebraMap _ _ (continuous_padicEmb (w := w) rfl)
local instance normalizationResidueFinite : Finite (LocalPadicLog.unitResidueField (completionAt K w)) :=
  integerResidue_finite w
local instance normalizationResidueCharP :
    CharP (LocalPadicLog.unitResidueField (completionAt K w)) (residueChar w) := integerResidue_charP w

private theorem normalization_norm_prime_lt_one : ‖(residueChar w : completionAt K w)‖ < 1 := by
  have h := norm_natCast_prime_lt_one (p := residueChar w) (w := w) rfl
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

theorem principalLogImage_eq_unitLog_image :
    (LocalPadicLog.principalLogImage (residueChar w) (normalization_norm_prime_lt_one w) :
      Set (completionAt K w)) = Set.range (fun a : (integerRing w)ˣ => unitLog w (Additive.ofMul a)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := (LocalPadicLog.mem_principalLogImage_iff _ _ z).mp hz
    let b : LocalPadicLog.principalUnits (k := completionAt K w) :=
      ⟨Units.mk0 a (LocalPadicLog.ne_zero_of_norm_sub_one_lt ha), ha⟩
    refine ⟨LocalPadicLog.principalToIntegerUnit b, ?_⟩
    exact unitLog_of_principal w _ ha
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := LocalPadicLog.integerUnitLog_has_principalRepresentative
      (Ω := AlgebraicClosure (completionAt K w)) (residueChar w) (normalization_norm_prime_lt_one w) a
    exact (LocalPadicLog.mem_principalLogImage_iff _ _ _).mpr ⟨b.1, b.2, hb⟩

theorem unitLog_image_ssubset_logShell :
    Set.range (fun a : (integerRing w)ˣ => unitLog w (Additive.ofMul a)) ⊂
      LocalPadicLog.logShell (k := completionAt K w) (residueChar w) := by
  rw [← principalLogImage_eq_unitLog_image]
  exact LocalPadicLog.principalLogImage_ssubset_logShell _ _

theorem paperScale_mul_logShell_eq_unitLog_image :
    (fun z : completionAt K w => (LocalPadicLog.paperScale (residueChar w) : completionAt K w) * z) ''
      LocalPadicLog.logShell (residueChar w) =
        Set.range (fun a : (integerRing w)ˣ => unitLog w (Additive.ofMul a)) := by
  rw [← principalLogImage_eq_unitLog_image]
  exact LocalPadicLog.paperScale_mul_logShell_eq_principalLogImage _ _

theorem exists_shell_class_without_integralLift :
    let S := LocalPadicLog.saturatedKummerPadicSubmodule (k := completionAt K w)
      (Ω := AlgebraicClosure (completionAt K w)) (residueChar w) (normalization_norm_prime_lt_one w)
    ∃ x : S, x ∈ LocalPadicLog.normalizedKummerShell (residueChar w) (normalization_norm_prime_lt_one w) ∧
      ¬ ∃ y, LocalKummer.Rational.standardMap (residueChar w) y = x.1 :=
  LocalPadicLog.exists_shell_class_without_integralLift (Ω := AlgebraicClosure (completionAt K w)) _ _

end
end JoshiTeich.Act1Scene1.LocalCompletion
